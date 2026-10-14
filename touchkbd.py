#!/usr/bin/env python3
"""Swipe-typeable on-screen keyboard, typing via ydotool/uinput.

Exists because GNOME's OSK won't show for Chrome (shell-side interop bug,
protocol verified fine with WAYLAND_DEBUG=1) and uinput keystrokes work in
every app. The native OSK is disabled by the no-auto-osk shell extension.

Standard three-screen layout, Gboard-style:
  letters  ->  ?123 (numbers + common punctuation)  ->  #+= (rest)
Letters screen supports swipe typing (SHARK2-lite over the top 10k of the
wordlist). Tap typing gets prefix completions, next-word suggestions after
space, and conservative one-edit autocorrect on space; hunspell-valid words
are never corrected. Learns from use (usage.json: counts of dictionary
words, word pairs, undone corrections). Backspace right after an
autocorrect reverts it for good; tap "+ word" in the bar to teach a new
word. ?123 -> Fn has F1-F12 and Home/End/Ins/PgUp/PgDn.
On-screen Shift also applies to tab/enter/arrows (shift+tab cycles Claude
Code permission modes). Collapses to a bottom-edge pill with scroll keys;
auto-collapses after 20s idle.
"""
import bisect, ctypes, ctypes.util, fcntl, glob, json, math, os, socket, struct
import subprocess, sys, threading, time
os.environ["GDK_BACKEND"] = "x11"
import gi
gi.require_version("Gtk", "3.0")
gi.require_version("GdkX11", "3.0")
from gi.repository import Gtk, Gdk, GdkX11, GLib

SOCKET = os.environ.get("YDOTOOL_SOCKET",
                        "/run/user/%d/.ydotool_socket" % os.getuid())
WORDS = os.path.expanduser("~/.local/share/touchkbd/words.txt")
USER_WORDS = os.path.expanduser("~/.local/share/touchkbd/user-words.txt")
USAGE = os.path.expanduser("~/.local/share/touchkbd/usage.json")
SWIPE_MAX_RANK = 10000  # swipe DTW is O(cands); tap typing uses the full list
SHADOW_MAX = 400        # chars of our own typed text kept for context
SHIFT = 42
KEY_CAPSLOCK = 58
REPEAT_DELAY, REPEAT_MS = 420, 90
RESAMPLE = 24
TAP_SLOP = 26
FREQ_W = 3.5
IDLE_S = 20
PILL_KEY_W = 90         # collapsed-bar key width (logical px)
BKSP_GUARD_S = 0.6      # Enter's top half reads as Bksp this soon after one

KEYCODE = {c: i for i, c in enumerate(
    ["", "esc", "1", "2", "3", "4", "5", "6", "7", "8", "9", "0", "-", "=",
     "bksp", "tab", "q", "w", "e", "r", "t", "y", "u", "i", "o", "p", "[",
     "]", "enter", "ctrl", "a", "s", "d", "f", "g", "h", "j", "k", "l", ";",
     "'", "`", "lshift", "\\", "z", "x", "c", "v", "b", "n", "m", ",", ".",
     "/"])}
KEYCODE.update(space=57, up=103, down=108, left=105, right=106,
               pageup=104, pagedown=109, delete=111, home=102, end=107,
               insert=110)
for _i in range(10):
    KEYCODE["f%d" % (_i + 1)] = 59 + _i
KEYCODE.update(f11=87, f12=88)
# nav keys that honor the on-screen Shift (shift+tab cycles Claude Code
# permission modes; shift+arrows selects)
SHIFTABLE = {KEYCODE[k] for k in
             ("tab", "enter", "up", "down", "left", "right", "delete",
              "home", "end")}
AUTOCORRECT_MAX = 1.55
MIC_WAV = os.path.expanduser("~/.local/share/touchkbd/mic.wav")
_WHISPER = None

# char -> (keyname, shifted)
CHARS = {}
for c in "abcdefghijklmnopqrstuvwxyz1234567890":
    CHARS[c] = (c, False)
for c, k in [(",", ","), (".", "."), ("/", "/"), (";", ";"), ("'", "'"),
             ("[", "["), ("]", "]"), ("\\", "\\"), ("-", "-"), ("=", "="),
             ("`", "`")]:
    CHARS[c] = (k, False)
for c, k in [("!", "1"), ("@", "2"), ("#", "3"), ("$", "4"), ("%", "5"),
             ("^", "6"), ("&", "7"), ("*", "8"), ("(", "9"), (")", "0"),
             ("_", "-"), ("+", "="), (":", ";"), ('"', "'"), ("<", ","),
             (">", "."), ("?", "/"), ("{", "["), ("}", "]"), ("|", "\\"),
             ("~", "`")]:
    CHARS[c] = (k, True)

# Layouts: rows of (id, label, weight). Special ids: SHIFT BKSP SPACE ENTER
# GO:<screen> K:<keyname>. Everything else is a literal character.
LAYOUTS = {
    "letters": [
        [(c, c, 1) for c in "qwertyuiop"] + [("BKSP", "Bksp", 1.6)],
        [("PAD", "", 0.3)] + [(c, c, 1) for c in "asdfghjkl"] +
        [(";", ";", 1)] + [("ENTER", "Enter", 1.8)],
        [("SHIFT", "Shift", 1.6)] + [(c, c, 1) for c in "zxcvbnm"] +
        [(",", ",", 1), (".", ".", 1), ("/", "/", 1)],
        [("GO:sym1", "?123", 1.6), ("'", "'", 1), ("SPACE", "", 6),
         ("-", "-", 1), ("=", "=", 1)],
    ],
    "sym1": [
        [(c, c, 1) for c in "1234567890"] + [("BKSP", "Bksp", 1.6)],
        [(c, c, 1) for c in '-/:;()$&@"'] + [("ENTER", "Enter", 1.6)],
        [("GO:sym2", "#+=", 1.6), (".", ".", 1), (",", ",", 1),
         ("?", "?", 1), ("!", "!", 1), ("'", "'", 1), ("`", "`", 1),
         ("GO:fn", "Fn", 1.6)],
        [("GO:letters", "abc", 1.6), ("SPACE", "", 7)],
    ],
    "sym2": [
        [(c, c, 1) for c in "[]{}#%^*+="] + [("BKSP", "Bksp", 1.6)],
        [(c, c, 10 / 7) for c in "_\\|~<>`"] + [("ENTER", "Enter", 1.6)],
        [("GO:sym1", "?123", 1.6), (".", ".", 1), (",", ",", 1),
         ("?", "?", 1), ("!", "!", 1), ("'", "'", 1)],
        [("GO:letters", "abc", 1.6), ("SPACE", "", 7)],
    ],
    "fn": [
        [("K:f%d" % i, "F%d" % i, 1) for i in range(1, 7)] +
        [("K:esc", "Esc", 1)],
        [("K:f%d" % i, "F%d" % i, 1) for i in range(7, 13)] +
        [("K:delete", "Del", 1)],
        [("K:home", "Home", 1), ("K:end", "End", 1), ("K:insert", "Ins", 1),
         ("K:pageup", "PgUp", 1), ("K:pagedown", "PgDn", 1)],
        [("GO:letters", "abc", 1.6), ("GO:sym1", "?123", 1.6),
         ("SPACE", "", 4), ("ENTER", "Enter", 1.6)],
    ],
}


class Injector:
    """Writes input_event structs straight to ydotoold's datagram socket.
    A ydotool subprocess per keystroke cost 30-80ms on the UI thread; a
    datagram is microseconds. Falls back to the CLI if the socket dies."""

    def __init__(self, path):
        self.path = path
        self.sock = None

    def send(self, codes):
        for _attempt in (0, 1):
            try:
                if self.sock is None:
                    self.sock = socket.socket(socket.AF_UNIX,
                                              socket.SOCK_DGRAM)
                    self.sock.connect(self.path)
                for code, val in codes:
                    self.sock.send(struct.pack("llHHi", 0, 0, 1, code, val))
                    self.sock.send(struct.pack("llHHi", 0, 0, 0, 0, 0))
                return
            except OSError:
                if self.sock:
                    self.sock.close()
                self.sock = None
        env = dict(os.environ, YDOTOOL_SOCKET=self.path)
        subprocess.run(["ydotool", "key"] + ["%d:%d" % c for c in codes],
                       env=env, capture_output=True, text=True, timeout=5)


INJ = Injector(SOCKET)

BTN_LEFT, BTN_RIGHT, BTN_MIDDLE = 0x110, 0x111, 0x112
MOUSE_GAIN = 1.2


class VirtualMouse:
    """Transient uinput pointer for mouse mode (terminal text selection —
    VTE has no touch selection at all; long-press only opens its menu).
    The device must NOT outlive the mode: a persistent pointer makes
    Mutter drop touch-mode, which kills auto-rotation. /dev/uinput access
    comes from the uaccess udev rule in /etc/udev/rules.d/."""

    UI_SET_EVBIT, UI_SET_KEYBIT = 0x40045564, 0x40045565
    UI_SET_RELBIT = 0x40045566
    UI_DEV_CREATE, UI_DEV_DESTROY = 0x5501, 0x5502

    def __init__(self):
        self.fd = os.open("/dev/uinput",
                          os.O_WRONLY | os.O_NONBLOCK | os.O_CLOEXEC)
        for ev in (1, 2, 0):  # EV_KEY, EV_REL, EV_SYN
            fcntl.ioctl(self.fd, self.UI_SET_EVBIT, ev)
        for b in (BTN_LEFT, BTN_RIGHT, BTN_MIDDLE):
            fcntl.ioctl(self.fd, self.UI_SET_KEYBIT, b)
        for r in (0, 1):  # REL_X, REL_Y
            fcntl.ioctl(self.fd, self.UI_SET_RELBIT, r)
        os.write(self.fd, struct.pack("80sHHHHi", b"touchkbd pointer",
                                      0x06, 0x2333, 0x6667, 1, 0)
                 + b"\0" * 1024)
        fcntl.ioctl(self.fd, self.UI_DEV_CREATE)
        self.held = False

    def _emit(self, t, c, v):
        os.write(self.fd, struct.pack("llHHi", 0, 0, t, c, v))

    def move(self, dx, dy):
        if dx:
            self._emit(2, 0, dx)
        if dy:
            self._emit(2, 1, dy)
        self._emit(0, 0, 0)

    def button(self, btn, val):
        self._emit(1, btn, val)
        self._emit(0, 0, 0)
        if btn == BTN_LEFT:
            self.held = bool(val)

    def click(self, btn=BTN_LEFT, times=1):
        for _ in range(times):
            self.button(btn, 1)
            self.button(btn, 0)

    def close(self):
        if self.held:
            self.button(BTN_LEFT, 0)
        fcntl.ioctl(self.fd, self.UI_DEV_DESTROY)
        os.close(self.fd)


def send(codes):
    INJ.send(codes)


def char_codes(ch, force_shift=False):
    key, shifted = CHARS[ch]
    c = KEYCODE[key]
    if shifted or force_shift:
        return [(SHIFT, 1), (c, 1), (c, 0), (SHIFT, 0)]
    return [(c, 1), (c, 0)]


def type_word(word, capitalize=False):
    codes = []
    for i, ch in enumerate(word):
        codes += char_codes(ch, force_shift=(capitalize and i == 0))
    codes += [(KEYCODE["space"], 1), (KEYCODE["space"], 0)]
    send(codes)


_UNICODE_FOLD = {"’": "'", "‘": "'", "“": '"',
                 "”": '"', "—": "-", "–": "-",
                 "…": "..."}


def type_text(text):
    """Inject free-form text (speech transcripts). Whisper's curly quotes
    map to their ASCII forms; anything still unmapped is dropped rather
    than mistyped. Sent in small paced chunks — one giant burst can lose
    keystrokes in the receiving app."""
    for u, a in _UNICODE_FOLD.items():
        text = text.replace(u, a)
    codes = []
    for ch in text:
        if ch == "\n":
            codes += [(KEYCODE["enter"], 1), (KEYCODE["enter"], 0)]
        elif ch == " ":
            codes += [(KEYCODE["space"], 1), (KEYCODE["space"], 0)]
        elif ch.lower() in CHARS:
            codes += char_codes(ch.lower(), force_shift=ch.isupper())
    for i in range(0, len(codes), 16):
        send(codes[i:i + 16])
        time.sleep(0.01)


def resample(pts, n=RESAMPLE):
    if len(pts) == 1:
        return pts * n
    dists = [0.0]
    for i in range(1, len(pts)):
        dists.append(dists[-1] + math.dist(pts[i - 1], pts[i]))
    total = dists[-1]
    if total == 0:
        return [pts[0]] * n
    out, j = [], 0
    for k in range(n):
        target = total * k / (n - 1)
        while j < len(dists) - 2 and dists[j + 1] < target:
            j += 1
        seg = dists[j + 1] - dists[j]
        t = 0 if seg == 0 else (target - dists[j]) / seg
        out.append((pts[j][0] + (pts[j + 1][0] - pts[j][0]) * t,
                    pts[j][1] + (pts[j + 1][1] - pts[j][1]) * t))
    return out


class Decoder:
    def __init__(self, centers):
        self.centers = centers
        self.index = {}
        seen = set()
        if os.path.exists(USER_WORDS):        # personal lexicon, high priority
            with open(USER_WORDS) as f:
                for line in f:
                    w = line.strip().lower()
                    if len(w) >= 2 and w not in seen and \
                       all(c in centers for c in w):
                        seen.add(w)
                        self.index.setdefault((w[0], w[-1]), []).append((w, 300))
        if os.path.exists(WORDS):
            with open(WORDS) as f:
                for rank, line in enumerate(f):
                    if rank >= SWIPE_MAX_RANK:
                        break
                    w = line.strip()
                    if len(w) >= 2 and w not in seen and \
                       all(c in centers for c in w):
                        self.index.setdefault((w[0], w[-1]), []).append((w, rank))

    def near(self, pt, radius):
        return [l for l, c in self.centers.items() if math.dist(pt, c) <= radius]

    def ideal(self, word):
        pts, last = [], None
        for ch in word:
            if ch != last:
                pts.append(self.centers[ch])
            last = ch
        return resample(pts)

    @staticmethod
    def _dtw(a, b):
        """Elastic match: mean cost along the optimal warping path."""
        n, m = len(a), len(b)
        INF = float("inf")
        prev = [INF] * (m + 1)
        prev[0] = 0.0
        for i in range(1, n + 1):
            cur = [INF] * (m + 1)
            ai = a[i - 1]
            for j in range(1, m + 1):
                c = math.dist(ai, b[j - 1])
                cur[j] = c + min(prev[j], cur[j - 1], prev[j - 1])
            prev = cur
        return prev[m] / (n + m)

    @staticmethod
    def _norm(pts):
        """Translate to centroid, scale longest bbox side to 1 (shape channel)."""
        xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
        cx, cy = sum(xs) / len(xs), sum(ys) / len(ys)
        span = max(max(xs) - min(xs), max(ys) - min(ys), 1e-6)
        return [((x - cx) / span, (y - cy) / span) for x, y in pts]

    @staticmethod
    def _corners(pts, step=3, thresh=45):
        """Interior direction changes sharper than thresh degrees."""
        n = 0
        i = step
        while i < len(pts) - step:
            ax, ay = (pts[i][0] - pts[i - step][0], pts[i][1] - pts[i - step][1])
            bx, by = (pts[i + step][0] - pts[i][0], pts[i + step][1] - pts[i][1])
            la, lb = math.hypot(ax, ay), math.hypot(bx, by)
            if la > 4 and lb > 4:
                cos = max(-1, min(1, (ax * bx + ay * by) / (la * lb)))
                if math.degrees(math.acos(cos)) > thresh:
                    n += 1
                    i += step          # a sharp turn spans several samples
            i += 1
        return n

    def _word_corners(self, word):
        pts, last = [], None
        for ch in word:
            if ch != last:
                pts.append(self.centers[ch])
            last = ch
        n = 0
        for i in range(1, len(pts) - 1):
            ax, ay = (pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1])
            bx, by = (pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1])
            la, lb = math.hypot(ax, ay), math.hypot(bx, by)
            if la > 1 and lb > 1:
                cos = max(-1, min(1, (ax * bx + ay * by) / (la * lb)))
                if math.degrees(math.acos(cos)) > 45:
                    n += 1
        return n

    @staticmethod
    def _plen(pts):
        return sum(math.dist(pts[i - 1], pts[i]) for i in range(1, len(pts)))

    def decode(self, path, key_w, bonus=None):
        """bonus(word) -> learned-usage credit in log10-rank units."""
        sampled = resample(path)
        swipe_len = self._plen(sampled)
        s_shape = self._norm(sampled)
        s_corners = self._corners(sampled)
        # first/last touch events can lag the finger; anchor on the first
        # and last few resampled points, generous radius
        starts = set()
        for pt in sampled[:2]:
            starts.update(self.near(pt, key_w * 1.5))
        ends = set()
        for pt in sampled[-2:]:
            ends.update(self.near(pt, key_w * 1.5))
        cands = []
        for a in starts:
            for b in ends:
                cands.extend(self.index.get((a, b), []))
        scored = []
        for w, rank in cands:
            ip = self.ideal(w)
            # prune wildly wrong path lengths before paying for DTW
            if swipe_len > key_w:
                r = self._plen(ip) / swipe_len
                if not 0.45 < r < 2.2:
                    continue
            loc = self._dtw(sampled, ip)
            shape = self._dtw(s_shape, self._norm(ip)) * key_w
            ends_pen = (math.dist(sampled[0], ip[0]) +
                        math.dist(sampled[-1], ip[-1])) / 2
            score = (loc + 0.6 * shape + 1.2 * ends_pen +
                     0.35 * key_w * abs(s_corners - self._word_corners(w)) +
                     FREQ_W * (math.log10(rank + 10) -
                               (bonus(w) if bonus else 0.0)))
            scored.append((score, w))
        scored.sort()
        print("swipe: %d pts, len %.0f, start(%.0f,%.0f)->%s end(%.0f,%.0f)->%s, %d cands, top: %s"
              % (len(path), swipe_len, path[0][0], path[0][1], sorted(starts),
                 path[-1][0], path[-1][1], sorted(ends), len(cands),
                 [(w, round(sc, 1)) for sc, w in scored[:5]]), flush=True)
        seen, out = set(), []
        for _s, w in scored:
            if w not in seen:
                seen.add(w)
                out.append(w)
            if len(out) == 5:
                break
        return out


class Usage:
    """What you actually type: word counts, word->next-word counts, and
    autocorrections you undid. Only dictionary words are counted, so
    passwords and other random strings never reach disk."""

    def __init__(self, path=USAGE):
        self.path = path
        self.counts, self.bigrams, self.never = {}, {}, {}
        try:
            with open(path) as f:
                d = json.load(f)
            self.counts = d.get("counts", {})
            self.bigrams = d.get("bigrams", {})
            self.never = {k: set(v) for k, v in d.get("never", {}).items()}
        except (OSError, ValueError):
            pass
        self.dirty = False

    def note(self, w, prev=None, n=1):
        self.counts[w] = max(0, self.counts.get(w, 0) + n)
        if prev:
            nxt = self.bigrams.setdefault(prev, {})
            nxt[w] = max(0, nxt.get(w, 0) + n)
        self.dirty = True

    def reject(self, typed, corr):
        self.never.setdefault(typed, set()).add(corr)
        self.dirty = True

    def save(self):
        if not self.dirty:
            return
        os.makedirs(os.path.dirname(self.path), exist_ok=True)
        tmp = self.path + ".tmp"
        with open(tmp, "w") as f:
            json.dump({"counts": self.counts, "bigrams": self.bigrams,
                       "never": {k: sorted(v) for k, v in self.never.items()}},
                      f)
        os.replace(tmp, self.path)
        self.dirty = False


class Speller:
    """Persistent `hunspell -a` pipe: a backstop so real words that aren't
    in words.txt (paused, woken) never get autocorrected."""

    def __init__(self):
        self.proc, self.cache = None, {}

    def ok(self, w):
        if w in self.cache:
            return self.cache[w]
        res = False
        try:
            if self.proc is None:
                self.proc = subprocess.Popen(
                    ["hunspell", "-a", "-d", "en_US"], stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, text=True, bufsize=1)
                self.proc.stdout.readline()             # version banner
            self.proc.stdin.write("^%s\n" % w)
            lines = []
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    raise OSError("hunspell exited")
                if line == "\n":
                    break
                lines.append(line)
            first = lines[0] if lines else ""
            if first[:1] in "*+-":
                res = True
            elif first.startswith("&"):         # proper noun typed lowercase
                sugg = first.split(":", 1)[-1].strip().split(", ")
                res = w.capitalize() in sugg
        except (OSError, IndexError) as e:
            print("speller: %r" % e, flush=True)
            self.proc = None
            return False
        self.cache[w] = res
        return res


class Predictor:
    """Prefix completion, next-word prediction and conservative one-edit
    typo correction for tap typing. Ranking blends the static frequency
    list with what you actually type (Usage). Typo costs are typo-shaped:
    adjacent-key substitution and transposed letters are cheap, anything
    else must be a very common word before autocorrect fires (this
    keyboard mostly types into terminals)."""

    def __init__(self, centers, key_w, usage=None):
        self.centers = centers
        self.key_w = key_w
        self.usage = usage or Usage()
        self.speller = Speller()
        self.rank = {}
        self.user = set()
        if os.path.exists(USER_WORDS):
            with open(USER_WORDS) as f:
                for line in f:
                    w = line.strip().lower()
                    if len(w) >= 2 and w.isalpha() and w not in self.rank:
                        self.rank[w] = 300
                        self.user.add(w)
        if os.path.exists(WORDS):
            with open(WORDS) as f:
                for r, line in enumerate(f):
                    w = line.strip()
                    if w and w not in self.rank:
                        self.rank[w] = r
        self.sorted_words = sorted(self.rank)
        self.del1 = {}
        for w in self.rank:
            for d in self._dels(w):
                self.del1.setdefault(d, []).append(w)

    @staticmethod
    def _dels(w):
        return {w[:i] + w[i + 1:] for i in range(len(w))}

    def knows(self, w):
        return w in self.rank

    def valid(self, w):
        """A real word: in our lexicon or accepted by hunspell."""
        return w in self.rank or self.speller.ok(w)

    def learn(self, w):
        w = w.lower()
        if not w.isalpha() or len(w) < 2 or w in self.rank:
            return False
        self.rank[w] = 300
        self.user.add(w)
        bisect.insort(self.sorted_words, w)
        for d in self._dels(w):
            self.del1.setdefault(d, []).append(w)
        os.makedirs(os.path.dirname(USER_WORDS), exist_ok=True)
        with open(USER_WORDS, "a") as f:
            f.write(w + "\n")
        return True

    def bonus(self, w, prev=None):
        """Learned credit in log10-rank units: each doubling of your own
        use counts like ~2x more common; a seen word pair counts more."""
        b = 0.35 * math.log2(1 + self.usage.counts.get(w, 0))
        if prev:
            b += 0.6 * math.log2(1 + self.usage.bigrams.get(prev, {}).get(w, 0))
        return b

    def _score(self, w, prev):
        return math.log10(self.rank[w] + 10) - self.bonus(w, prev)

    def complete(self, prefix, prev=None, n=5):
        if not prefix:
            return []
        lo = bisect.bisect_left(self.sorted_words, prefix)
        hi = bisect.bisect_left(self.sorted_words, prefix + "￿")
        return sorted(self.sorted_words[lo:hi],
                      key=lambda w: self._score(w, prev))[:n]

    def next_words(self, prev, n=5):
        nxt = self.usage.bigrams.get(prev or "", {})
        ws = [w for w, c in nxt.items() if c > 0 and w in self.rank]
        return sorted(ws, key=lambda w: self._score(w, prev))[:n]

    def _adjacent(self, a, b):
        ca, cb = self.centers.get(a), self.centers.get(b)
        return bool(ca and cb and math.dist(ca, cb) <= self.key_w * 1.3)

    def _cost(self, typed, cand):
        if len(typed) == len(cand):
            diff = [(a, b) for a, b in zip(typed, cand) if a != b]
            if len(diff) == 1:
                return 0.5 if self._adjacent(*diff[0]) else 1.0
            if len(diff) == 2:
                (a1, b1), (a2, b2) = diff
                if a1 == b2 and a2 == b1:
                    return 0.6          # transposition
            return None
        if len(cand) == len(typed) - 1:
            return 0.7 if cand in self._dels(typed) else None
        if len(cand) == len(typed) + 1:
            if typed not in self._dels(cand):
                return None
            i = next((i for i, c in enumerate(typed) if c != cand[i]),
                     len(typed))
            # a dropped double letter (helo -> hello) is the commonest slip
            return 0.4 if cand[i] == cand[i - 1:i] or \
                cand[i] == cand[i + 1:i + 2] else 0.7
        return None

    def correct(self, typed, prev=None):
        """[(score, word)] within one edit of an unknown word, best first."""
        if len(typed) < 3 or not typed.isalpha() or self.knows(typed):
            return []
        cands = set()
        tdels = self._dels(typed)
        for d in tdels | {typed}:
            cands.update(self.del1.get(d, ()))
        cands.update(d for d in tdels if d in self.rank)
        cands -= self.usage.never.get(typed, set())
        scored = []
        for w in cands:
            c = self._cost(typed, w)
            if c is not None:
                # freq prior kept weak: it was letting common words (work,
                # world) beat the intended rarer word (worked) on typos
                scored.append((c + max(0.0, self._score(w, prev)) / 6.0, w))
        scored.sort()
        return scored[:4]


class Keyboard(Gtk.Window):
    def __init__(self):
        super().__init__(type=Gtk.WindowType.TOPLEVEL)
        self.set_title("touchkbd")
        for f in ("set_keep_above", "set_skip_taskbar_hint",
                  "set_skip_pager_hint"):
            getattr(self, f)(True)
        self.set_decorated(False)
        self.set_accept_focus(False)
        self.set_focus_on_map(False)
        self.set_type_hint(Gdk.WindowTypeHint.DOCK)
        GLib.timeout_add_seconds(2, self._reassert)

        self.mon = Gdk.Display.get_default().get_monitor(0).get_geometry()
        self.set_default_size(self.mon.width, -1)
        self.set_resizable(False)

        self.key_w = self.mon.width / 10.0
        self.key_h = 48
        self._screen = "letters"
        self._shift = 0
        # System Caps Lock (separate from our Shift lock). Read from the
        # kernel LED: GDK's keymap state never updates for an unfocused
        # Xwayland dock, but mutter mirrors xkb lock state to the LEDs.
        self._caps_led = next(iter(glob.glob(
            "/sys/class/leds/*capslock/brightness")), None)
        self._sys_caps = False
        GLib.timeout_add(500, self._poll_caps)
        self._timer = None
        self._idle_timer = None
        self._trail_timeout = None
        self._path = []
        self._down = False
        self._down_key = None
        self._last_commit = None
        self._last_bksp = 0.0
        # Our own typed text since the last focus-ambiguous action (cursor
        # keys, Enter, expand, mouse mode...). The word being typed and the
        # word before it are read from its tail, so backspacing into the
        # previous word picks it back up. Text we didn't type is invisible.
        self._shadow = ""
        self._last_auto = None          # (typed, corrected) until next key
        self._save_timer = None
        self._sugg_action = None
        self._rec_proc = None
        self._transcribing = False
        self.mouse = None
        self._pad_last = None
        self._pad_seq = None
        self._drag_pending = False
        self._drag_l_up = False
        self._drag_acc = [0, 0]
        self._pad_start = (0.0, 0.0, 0.0)
        self._pad_moved = 0.0
        self._pad_rx = self._pad_ry = 0.0

        self._layout_cache = {}
        for name in LAYOUTS:
            self._layout_cache[name] = self._compute_layout(name)
        self.keys = self._layout_cache["letters"]
        self.centers = {kid: (x + w / 2, y + h / 2)
                        for kid, x, y, w, h, _l in self._layout_cache["letters"]
                        if len(kid) == 1 and kid.isalpha()}
        self.decoder = Decoder(self.centers)
        self.usage = Usage()
        self.predictor = Predictor(self.centers, self.key_w, self.usage)
        self.canvas_h = 4 * self.key_h

        self.stack = Gtk.Stack()
        self.stack.set_hhomogeneous(False)
        self.stack.set_vhomogeneous(False)
        self.stack.add_named(self._build_body(), "body")
        self.stack.add_named(self._build_mouse(), "mouse")
        self.stack.add_named(self._build_pill(), "pill")
        self.add(self.stack)

        css = Gtk.CssProvider()
        css.load_from_data(b"""
        window, .kbd { background: rgba(16,16,20,0.97); }
        button { font-size: 15px; color: #f0f0f5; padding: 0; margin: 0;
                 background: rgba(44,44,54,1); min-height: 40px;
                 border: 1px solid rgba(0,0,0,0.55); border-radius: 7px; }
        button:active { background: #7878c8; }
        button.sugg { min-height: 36px; font-size: 16px;
                      background: rgba(34,34,44,1); border: none; }
        button.pill { min-height: 30px; font-size: 14px;
                      background: rgba(44,44,54,0.9); }
        button.rec { background: #a03030; }
        """)
        Gtk.StyleContext.add_provider_for_screen(
            Gdk.Screen.get_default(), css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)

        self.connect("size-allocate", self._dock)
        self.connect("delete-event", lambda *_: Gtk.main_quit())
        try:                            # save usage.json on tk-restart's pkill
            gi.require_version("GLibUnix", "2.0")
            from gi.repository import GLibUnix
            GLibUnix.signal_add(GLib.PRIORITY_DEFAULT, 15, self._on_term)
        except (ImportError, ValueError):
            GLib.unix_signal_add(GLib.PRIORITY_DEFAULT, 15, self._on_term)
        # rotation: geometry is baked into the layouts, so relaunch clean
        Gdk.Screen.get_default().connect("size-changed", self._on_rotate)

    def _on_rotate(self, *_):
        mon = Gdk.Display.get_default().get_monitor(0).get_geometry()
        if (mon.width, mon.height) != (self.mon.width, self.mon.height):
            print("rotation: %dx%d -> %dx%d, relaunching" %
                  (self.mon.width, self.mon.height, mon.width, mon.height),
                  flush=True)
            os.execv(sys.executable, [sys.executable, os.path.abspath(__file__)])

    def _compute_layout(self, name):
        keys = []
        for r, row in enumerate(LAYOUTS[name]):
            total = sum(w for _i, _l, w in row)
            unit = self.mon.width / total
            x, y = 0, r * self.key_h
            for kid, label, weight in row:
                w = weight * unit
                if kid != "PAD":
                    keys.append((kid, x, y, w, self.key_h, label))
                x += w
        if name == "letters":
            self.key_w = next(w for kid, _x, _y, w, _h, _l in keys
                              if kid == "q")
        return keys

    def _key_at(self, x, y):
        for kid, kx, ky, kw, kh, _l in self.keys:
            if kx <= x < kx + kw and ky <= y < ky + kh:
                return kid
        return None

    # ----- widgets -----

    def _build_body(self):
        v = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=3)
        v.get_style_context().add_class("kbd")
        v.set_border_width(3)

        # Fixed-height bar with recycled buttons: hiding/showing the bar
        # resized the window, which re-docked and re-published the strut on
        # every keystroke.
        self.sugg_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=4)
        self.sugg_box.set_size_request(-1, 40)
        self._sugg_btns = []
        for _ in range(5):
            b = Gtk.Button()
            b.get_style_context().add_class("sugg")
            b.set_no_show_all(True)
            b.connect("clicked", self._on_sugg)
            self._sugg_btns.append(b)
            self.sugg_box.pack_start(b, True, True, 0)
        v.pack_start(self.sugg_box, False, False, 0)

        self.canvas = Gtk.DrawingArea()
        self.canvas.set_size_request(self.mon.width, self.canvas_h)
        self.canvas.add_events(Gdk.EventMask.BUTTON_PRESS_MASK |
                               Gdk.EventMask.BUTTON_RELEASE_MASK |
                               Gdk.EventMask.POINTER_MOTION_MASK)
        self.canvas.connect("draw", self._draw)
        self.canvas.connect("button-press-event", self._canvas_press)
        self.canvas.connect("motion-notify-event", self._canvas_motion)
        self.canvas.connect("button-release-event", self._canvas_release)
        v.pack_start(self.canvas, False, False, 0)

        nav = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=3)
        # Order matters: the keys under the spacebar must be harmless on a
        # missed tap (scroll/hide), and Up -- which recalls shell history --
        # sits at the far right edge under "=".
        nav.pack_start(self._btn("esc", lambda *_: self._tap(KEYCODE["esc"])), True, True, 0)
        self._tab_btn = self._btn("tab", lambda *_: self._tap(KEYCODE["tab"]))
        nav.pack_start(self._tab_btn, True, True, 0)
        self._mic_btns = []
        nav.pack_start(self._new_mic_btn(), True, True, 0)
        # copy/paste: plain = ctrl+c/v, with on-screen Shift = ctrl+shift+c/v
        # (the terminal variant), matching how Shift maps onto the nav keys.
        nav.pack_start(self._btn("copy", self._copy), True, True, 0)
        nav.pack_start(self._btn("paste", self._paste), True, True, 0)
        nav.pack_start(self._btn("🖱", self._mouse_toggle), True, True, 0)
        nav.pack_start(self._btn("⌦", None, code=KEYCODE["delete"], repeat=True), True, True, 0)
        nav.pack_start(self._btn("⇞", None, code=KEYCODE["pageup"], repeat=True), True, True, 0)
        nav.pack_start(self._btn("⇟", None, code=KEYCODE["pagedown"], repeat=True), True, True, 0)
        nav.pack_start(self._btn("hide ▾", self._collapse), True, True, 0)
        for lbl, code in (("◀", KEYCODE["left"]), ("▼", KEYCODE["down"]),
                          ("▲", KEYCODE["up"]), ("▶", KEYCODE["right"])):
            nav.pack_start(self._btn(lbl, None, code=code, repeat=True), True, True, 0)
        v.pack_start(nav, False, False, 0)
        return v

    def _build_mouse(self):
        v = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=3)
        v.get_style_context().add_class("kbd")
        v.set_border_width(3)
        self.pad = Gtk.DrawingArea()
        self.pad.set_size_request(self.mon.width, self.canvas_h + 43)
        # Touch events, not emulated pointer events: the drag button is
        # held by one finger while a second strokes the pad, and only the
        # first touch sequence gets pointer emulation.
        self.pad.add_events(Gdk.EventMask.BUTTON_PRESS_MASK |
                            Gdk.EventMask.BUTTON_RELEASE_MASK |
                            Gdk.EventMask.POINTER_MOTION_MASK |
                            Gdk.EventMask.TOUCH_MASK)
        self.pad.connect("draw", self._pad_draw)
        self.pad.connect("touch-event", self._pad_touch)
        self.pad.connect("button-press-event", self._pad_press)
        self.pad.connect("motion-notify-event", self._pad_motion)
        self.pad.connect("button-release-event", self._pad_release)
        v.pack_start(self.pad, False, False, 0)
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=3)
        # L/R are touch-native areas, NOT GtkButtons: a GtkButton touch goes
        # through pointer emulation, which WARPS the pointer to the button —
        # the drag anchor landed on the keyboard instead of the target text.
        self._lbtn = self._mouse_btn("L  (hold = drag)", self._drag_set)
        row.pack_start(self._lbtn, True, True, 0)
        self._rbtn = self._mouse_btn("R", self._rclick_set)
        row.pack_start(self._rbtn, True, True, 0)
        self._mbtn_paste = self._mouse_btn("M paste", self._mclick_set)
        row.pack_start(self._mbtn_paste, True, True, 0)
        # Ctrl latch: the next tap-click goes out as Ctrl+click — Ptyxis
        # opens links only on Ctrl+click (its capture-phase handler runs
        # before VTE, so this works under TUI mouse reporting too)
        self._cbtn = self._mouse_btn("Ctrl  (link)", self._ctrl_set)
        self._cbtn._latched = False
        row.pack_start(self._cbtn, True, True, 0)
        row.pack_start(self._btn("⌨ back", self._mouse_exit), True, True, 0)
        v.pack_start(row, False, False, 0)
        return v

    def _mouse_btn(self, label, setter):
        da = Gtk.DrawingArea()
        da.set_size_request(-1, 44)
        # touch events only arrive when the button masks are selected too
        da.add_events(Gdk.EventMask.TOUCH_MASK |
                      Gdk.EventMask.BUTTON_PRESS_MASK |
                      Gdk.EventMask.BUTTON_RELEASE_MASK)
        da._label, da._down = label, False
        da.connect("draw", self._mouse_btn_draw)
        da.connect("touch-event", self._mouse_btn_touch, setter)
        return da

    def _mouse_btn_draw(self, w, cr):
        a = w.get_allocation()
        on = w._down or getattr(w, "_latched", False)
        col = (0.47, 0.47, 0.78, 1) if on else (0.17, 0.17, 0.22, 1)
        cr.set_source_rgba(*col)
        self._round_rect(cr, 2, 2, a.width - 4, a.height - 4, 7)
        cr.fill()
        cr.set_source_rgba(0.94, 0.94, 0.96, 1)
        cr.set_font_size(15)
        ext = cr.text_extents(w._label)
        cr.move_to(a.width / 2 - ext.width / 2, a.height / 2 + ext.height / 2)
        cr.show_text(w._label)
        return False

    def _mouse_btn_touch(self, w, ev, setter):
        t = ev.type
        if t == Gdk.EventType.TOUCH_BEGIN:
            self._poke()
            if self.mouse and not w._down:
                w._down = True
                setter(True)
                w.queue_draw()
        elif t in (Gdk.EventType.TOUCH_END, Gdk.EventType.TOUCH_CANCEL):
            if w._down:
                w._down = False
                if self.mouse:
                    setter(False)
                w.queue_draw()
        return True

    def _rclick_set(self, on):
        # deferred for the same reason as the pad tap-click
        if not on:
            GLib.timeout_add(250, self._deferred_click, BTN_RIGHT)

    def _ctrl_set(self, on):
        if on:
            self._cbtn._latched = not self._cbtn._latched
            print("mouse: ctrl %s" % ("armed" if self._cbtn._latched
                                      else "off"), flush=True)

    def _mclick_set(self, on):
        # middle-click pastes the PRIMARY selection (what L-drag selected);
        # shift-wrapped so it pastes even under TUI mouse reporting
        if not on:
            GLib.timeout_add(400, self._deferred_mpaste)

    def _deferred_mpaste(self):
        if self.mouse:
            self._wiggle()
            send([(SHIFT, 1)])
            self.mouse.click(BTN_MIDDLE)
            send([(SHIFT, 0)])
        return False

    # ----- mouse mode -----

    def _mouse_toggle(self, *_):
        self._poke()
        self._reset_word()              # clicks move the cursor
        if self.mouse:
            return self._mouse_exit()
        try:
            self.mouse = VirtualMouse()
        except OSError as e:
            print("mouse: /dev/uinput failed: %s" % e, flush=True)
            return
        self._pad_last = None
        self.stack.set_visible_child_name("mouse")

    def _mouse_exit(self, *_):
        self._poke()
        self._mouse_teardown()
        self.stack.set_visible_child_name("body")

    def _mouse_teardown(self):
        self._drag_pending = self._drag_l_up = False
        if self.mouse:
            if self.mouse.held:
                send([(SHIFT, 0)])  # a replay may have shift down
            self.mouse.close()      # releases any held button
            self.mouse = None
            self._cbtn._latched = False
            for w in (self._lbtn, self._rbtn, self._mbtn_paste, self._cbtn):
                w._down = False
                w.queue_draw()

    def _mouse_do(self, fn):
        self._poke()
        if self.mouse:
            fn(self.mouse)

    def _drag_set(self, on):
        # The drag can't run while a finger is on the screen: active touch
        # steals pointer delivery from the target window (verified — the
        # same event stream selects fine with no touch down). So holding L
        # only RECORDS the sweep; _drag_replay re-executes it after both
        # fingers lift. Needs flat accel-profile so deltas replay exactly.
        if on:
            self._drag_pending = True
            self._drag_l_up = False
            self._drag_acc = [0, 0]
        else:
            self._drag_l_up = True
            self._maybe_replay()

    def _maybe_replay(self):
        if not (self._drag_pending and self._drag_l_up):
            return
        if self._pad_seq is not None:  # sweep finger still down
            return
        self._drag_pending = False
        self._drag_l_up = False
        ax, ay = self._drag_acc
        GLib.timeout_add(300, self._drag_replay, ax, ay)

    def _drag_replay(self, ax, ay):
        if not self.mouse:
            return False
        print("mouse: replay %d,%d" % (ax, ay), flush=True)
        m = self.mouse
        if ax == 0 and ay == 0:
            m.click()
            return False
        # Shift+drag, not plain drag: TUIs (Claude Code) turn on mouse
        # reporting, which swallows plain drags; Shift forces VTE's own
        # selection layer in both cases.
        m.move(-ax, -ay)  # rewind to the anchor
        time.sleep(0.06)
        # plain click first: at a plain prompt shift+drag EXTENDS any old
        # selection instead of starting one — the click clears it
        m.click()
        time.sleep(0.12)
        send([(SHIFT, 1)])
        m.button(BTN_LEFT, 1)
        time.sleep(0.06)
        steps, fx, fy = 16, 0, 0
        for i in range(1, steps + 1):
            tx, ty = ax * i // steps, ay * i // steps
            m.move(tx - fx, ty - fy)
            fx, fy = tx, ty
            time.sleep(0.015)
        time.sleep(0.06)
        m.button(BTN_LEFT, 0)
        send([(SHIFT, 0)])
        # promote the fresh PRIMARY selection to the CLIPBOARD so the
        # normal paste key works everywhere (VTE middle-click self-paste
        # is unreliable)
        GLib.timeout_add(250, self._sel_to_clipboard)
        return False

    def _sel_to_clipboard(self):
        Gtk.Clipboard.get(Gdk.SELECTION_PRIMARY).request_text(
            self._sel_got, None)
        return False

    def _sel_got(self, _cb, text, _data):
        if text:
            Gtk.Clipboard.get(Gdk.SELECTION_CLIPBOARD).set_text(text, -1)
            print("mouse: clipboard <- %d chars" % len(text), flush=True)
        else:
            print("mouse: clipboard promote: no primary text", flush=True)

    def _deferred_click(self, btn):
        if self.mouse:
            self._wiggle()
            if btn == BTN_LEFT and self._cbtn._latched:
                self._cbtn._latched = False   # one-shot
                self._cbtn.queue_draw()
                print("mouse: ctrl+click", flush=True)
                send([(KEYCODE["ctrl"], 1)])
                time.sleep(0.03)
                self.mouse.click(btn)
                time.sleep(0.03)
                send([(KEYCODE["ctrl"], 0)])
            else:
                self.mouse.click(btn)
        return False

    def _wiggle(self):
        # 1px out-and-back: after touch input the pointer's presence over
        # the window is stale, and the first click only re-establishes it —
        # a tiny move forces the compositor to re-deliver pointer focus
        self.mouse.move(1, 0)
        time.sleep(0.05)
        self.mouse.move(-1, 0)
        time.sleep(0.08)

    def _pad_draw(self, _w, cr):
        cr.set_source_rgba(0.06, 0.06, 0.08, 1)
        cr.paint()
        a = self.pad.get_allocation()
        cr.set_source_rgba(0.13, 0.13, 0.17, 1)
        self._round_rect(cr, 6, 6, a.width - 12, a.height - 12, 10)
        cr.fill()
        cr.set_source_rgba(0.45, 0.45, 0.52, 1)
        cr.set_font_size(15)
        for i, line in enumerate(
                ("trackpad — drag to move, tap to click",
                 "select: HOLD the drag key + sweep here with another finger")):
            ext = cr.text_extents(line)
            cr.move_to(a.width / 2 - ext.width / 2,
                       a.height / 2 + i * 26 - 8)
            cr.show_text(line)
        return False

    def _pad_begin(self, x, y):
        self._poke()
        self._pad_last = (x, y)
        self._pad_start = (x, y, time.time())
        self._pad_moved = 0.0
        self._pad_rx = self._pad_ry = 0.0

    def _pad_move(self, x, y):
        if self._pad_last is None or not self.mouse:
            return
        dx, dy = x - self._pad_last[0], y - self._pad_last[1]
        self._pad_last = (x, y)
        self._pad_moved += abs(dx) + abs(dy)
        self._pad_rx += dx * MOUSE_GAIN
        self._pad_ry += dy * MOUSE_GAIN
        mx, my = int(self._pad_rx), int(self._pad_ry)
        self._pad_rx -= mx
        self._pad_ry -= my
        if mx or my:
            self.mouse.move(mx, my)
            if self._drag_pending:
                self._drag_acc[0] += mx
                self._drag_acc[1] += my

    def _pad_end(self):
        if self._pad_last is None:
            return
        _x0, _y0, t0 = self._pad_start
        self._pad_last = None
        if self._drag_pending or self._drag_l_up:
            self._maybe_replay()
            return
        # deferred so the click fires with no finger on the screen —
        # active touch steals pointer delivery from the target window
        if (self.mouse and self._pad_moved <= TAP_SLOP
                and time.time() - t0 < 0.4):
            GLib.timeout_add(250, self._deferred_click, BTN_LEFT)

    def _pad_touch(self, _w, ev):
        t = ev.type
        if t == Gdk.EventType.TOUCH_BEGIN:
            if self._pad_seq is None:
                self._pad_seq = ev.touch.sequence
                self._pad_begin(ev.touch.x, ev.touch.y)
        elif t == Gdk.EventType.TOUCH_UPDATE:
            if ev.touch.sequence == self._pad_seq:
                self._pad_move(ev.touch.x, ev.touch.y)
        elif t in (Gdk.EventType.TOUCH_END, Gdk.EventType.TOUCH_CANCEL):
            if ev.touch.sequence == self._pad_seq:
                self._pad_seq = None
                self._pad_end()
        return True

    # pointer-event fallbacks (real mouse); touches are handled above, so
    # skip the pointer events GDK synthesizes from the primary touch
    def _pad_press(self, _w, ev):
        if not ev.get_pointer_emulated():
            self._pad_begin(ev.x, ev.y)
        return True

    def _pad_motion(self, _w, ev):
        if not ev.get_pointer_emulated() and self._pad_seq is None:
            self._pad_move(ev.x, ev.y)
        return True

    def _pad_release(self, _w, ev):
        if not ev.get_pointer_emulated() and self._pad_seq is None:
            self._pad_end()
        return True

    def _build_pill(self):
        h = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=4)
        b = Gtk.Button(label="⌨  keyboard")
        b.get_style_context().add_class("pill")
        b.connect("clicked", self._expand)
        h.pack_end(b, False, False, 0)
        for lbl, code in (("⇟", KEYCODE["pagedown"]), ("⇞", KEYCODE["pageup"])):
            sb = Gtk.Button(label=lbl)
            sb.get_style_context().add_class("pill")
            sb.set_size_request(PILL_KEY_W, -1)
            sb.connect("pressed", self._press_repeat, code)
            sb.connect("released", self._stop_repeat)
            sb.connect("leave", self._stop_repeat)
            h.pack_end(sb, False, False, 0)
        # tab / enter / mic usable without expanding the keyboard
        for lbl, code in (("⏎", KEYCODE["enter"]), ("tab", KEYCODE["tab"])):
            kb = Gtk.Button(label=lbl)
            kb.get_style_context().add_class("pill")
            kb.set_size_request(PILL_KEY_W, -1)
            kb.connect("clicked", lambda _b, c=code: self._tap(c))
            h.pack_end(kb, False, False, 0)
        mb = self._new_mic_btn()
        mb.get_style_context().add_class("pill")
        mb.set_size_request(PILL_KEY_W, -1)
        h.pack_end(mb, False, False, 0)
        # Claude Code slash commands, on the far left away from the keys
        # above. /clear wipes the session, so it takes a second tap.
        hb = Gtk.Button(label="handoff")
        hb.get_style_context().add_class("pill")
        hb.set_size_request(PILL_KEY_W, -1)
        hb.connect("clicked", lambda _b: self._slash("/handoff"))
        h.pack_start(hb, False, False, 0)
        self._clear_btn = Gtk.Button(label="clear")
        self._clear_btn.get_style_context().add_class("pill")
        self._clear_btn.set_size_request(PILL_KEY_W, -1)
        self._clear_btn.connect("clicked", self._clear_tap)
        h.pack_start(self._clear_btn, False, False, 0)
        self._clear_armed = None
        cb = Gtk.Button(label="claude")
        cb.get_style_context().add_class("pill")
        cb.set_size_request(PILL_KEY_W, -1)
        cb.connect("clicked", lambda _b: self._slash("claude"))
        h.pack_start(cb, False, False, 0)
        tb = Gtk.Button(label="bls")
        tb.get_style_context().add_class("pill")
        tb.set_size_request(PILL_KEY_W, -1)
        tb.connect("clicked", lambda _b: (self._reset_word(), type_text("bls")))
        h.pack_start(tb, False, False, 0)
        # landscape only: portrait has no room for another key
        if self.mon.width > self.mon.height:
            fb = Gtk.Button(label="touchpad")
            fb.get_style_context().add_class("pill")
            fb.set_size_request(PILL_KEY_W, -1)
            fb.connect("clicked", self._touchpad_fix)
            h.pack_start(fb, False, False, 0)
        return h

    def _touchpad_fix(self, b):
        """Log the dead-touchpad state and re-plug the Type Cover
        (~/bin/touchpad-fix -> touchpad-fix.service, surfacego-config)."""
        if b.get_label() != "touchpad":
            return
        subprocess.Popen([os.path.expanduser("~/bin/touchpad-fix")])
        b.set_label("fixing…")
        GLib.timeout_add(4000, lambda: b.set_label("touchpad") and False)

    def _slash(self, cmd):
        type_text(cmd)
        # let Claude Code's command menu settle before submitting
        GLib.timeout_add(250, lambda: self._tap(KEYCODE["enter"]) and False)

    def _clear_tap(self, _b):
        if self._clear_armed:
            GLib.source_remove(self._clear_armed)
            self._clear_disarm()
            self._slash("/clear")
            return
        self._clear_btn.set_label("clear?")
        self._clear_btn.get_style_context().add_class("rec")
        self._clear_armed = GLib.timeout_add_seconds(3, self._clear_disarm)

    def _clear_disarm(self):
        self._clear_armed = None
        self._clear_btn.set_label("clear")
        self._clear_btn.get_style_context().remove_class("rec")
        return False

    def _new_mic_btn(self):
        """All mic buttons (nav row + pill) share one recording state."""
        b = Gtk.Button(label="🎤")
        b.connect("clicked", self._mic_toggle)
        self._mic_btns.append(b)
        return b

    def _set_mic_label(self, label, rec=False):
        for b in self._mic_btns:
            b.set_label(label)
            ctx = b.get_style_context()
            if rec:
                ctx.add_class("rec")
            else:
                ctx.remove_class("rec")

    def _btn(self, label, cb, code=None, repeat=False):
        b = Gtk.Button(label=label)
        if repeat and code is not None:
            b.connect("pressed", self._press_repeat, code)
            b.connect("released", self._stop_repeat)
            b.connect("leave", self._stop_repeat)
        elif cb:
            b.connect("clicked", cb)
        return b

    def _set_suggestions(self, words, action=None, mark=None, add=None):
        """mark = the word now in the text; add = unknown word a tap
        will teach."""
        self._sugg_action = action or self._replace_last
        for b, w in zip(self._sugg_btns, words):
            b._word = w
            b.set_label(("\u2713 " + w) if w == mark else
                        ("+ " + w) if w == add else w)
            b.show()
        for b in self._sugg_btns[len(words):]:
            b.hide()

    def _on_sugg(self, b):
        self._poke()
        if self._sugg_action:
            self._sugg_action(b._word)

    # ----- drawing -----

    def _draw(self, _w, cr):
        cr.set_source_rgba(0.06, 0.06, 0.08, 1)
        cr.paint()
        up = (bool(self._shift) != self._sys_caps) and self._screen == "letters"
        for kid, x, y, w, h, label in self.keys:
            pressed = (kid == self._down_key and self._down)
            if kid == "SHIFT" and self._shift:
                pressed = True
            special = not (len(kid) == 1)
            if kid == "SHIFT" and self._sys_caps:
                col = (0.78, 0.22, 0.22, 1)      # system Caps Lock latched
            elif pressed:
                col = (0.47, 0.47, 0.78, 1)
            elif special:
                col = (0.17, 0.17, 0.22, 1)
            else:
                col = (0.24, 0.24, 0.29, 1)
            cr.set_source_rgba(*col)
            self._round_rect(cr, x + 2, y + 2, w - 4, h - 4, 7)
            cr.fill()
            if kid == "SHIFT":
                if self._sys_caps:
                    label = "CAPS"
                else:
                    label = "SHIFT" if self._shift == 2 else "Shift"
            elif kid == "SPACE":
                cr.set_source_rgba(0.55, 0.55, 0.60, 1)
                cr.rectangle(x + w * 0.25, y + h / 2 - 2, w * 0.5, 4)
                cr.fill()
            text = label.upper() if (up and not special) else label
            cr.set_source_rgba(0.94, 0.94, 0.96, 1)
            cr.set_font_size(13 if special and len(label) > 1 else 18)
            ext = cr.text_extents(text)
            cr.move_to(x + w / 2 - ext.width / 2, y + h / 2 + ext.height / 2)
            cr.show_text(text)
        if len(self._path) > 1 and self._screen == "letters":
            cr.set_source_rgba(0.55, 0.55, 0.95, 0.85)
            cr.set_line_width(5)
            cr.set_line_cap(1)
            cr.move_to(*self._path[0])
            for p in self._path[1:]:
                cr.line_to(*p)
            cr.stroke()
        return False

    @staticmethod
    def _round_rect(cr, x, y, w, h, r):
        cr.new_sub_path()
        cr.arc(x + w - r, y + r, r, -math.pi / 2, 0)
        cr.arc(x + w - r, y + h - r, r, 0, math.pi / 2)
        cr.arc(x + r, y + h - r, r, math.pi / 2, math.pi)
        cr.arc(x + r, y + r, r, math.pi, 3 * math.pi / 2)
        cr.close_path()

    # ----- canvas input -----

    def _canvas_press(self, _w, ev):
        self._poke()
        self._down = True
        self._path = [(ev.x, ev.y)]
        self._down_key = self._key_at(ev.x, ev.y)
        # Enter sits right under Bksp: a backspace run drifting down onto
        # Enter's top half stays a backspace.
        if (self._down_key == "ENTER"
                and time.monotonic() - self._last_bksp < BKSP_GUARD_S
                and self._key_at(ev.x, ev.y - self.key_h / 2) == "BKSP"):
            print("bksp guard: enter tap -> bksp", flush=True)
            self._down_key = "BKSP"
        if self._trail_timeout:
            GLib.source_remove(self._trail_timeout)
            self._trail_timeout = None
        if self._down_key == "BKSP":
            if self._undo_autocorrect():
                self.canvas.queue_draw()
                return True
            self._tap(KEYCODE["bksp"])
            self._stop_repeat()
            self._timer = GLib.timeout_add(REPEAT_DELAY, self._begin_repeat,
                                           KEYCODE["bksp"])
        self.canvas.queue_draw()
        return True

    def _canvas_motion(self, _w, ev):
        if self._down:
            self._path.append((ev.x, ev.y))
            if self._down_key == "BKSP" and self._key_at(ev.x, ev.y) != "BKSP":
                self._stop_repeat()
            self.canvas.queue_draw()
        return True

    def _canvas_release(self, _w, ev):
        if not self._down:
            return True
        self._down = False
        self._stop_repeat()
        path, key0 = self._path, self._down_key
        self._down_key = None
        span = max(math.dist(path[0], p) for p in path) if len(path) > 1 else 0

        if span <= TAP_SLOP:
            self._activate(key0)
            self._path = []
        elif (self._screen == "letters" and key0 and
              len(key0) == 1 and key0.isalpha()):
            prev = self._prev_word()
            words = self.decoder.decode(
                path, self.key_w,
                bonus=lambda w: self.predictor.bonus(w, prev))
            if words:
                cap = bool(self._shift)
                prev = self._prev_word()
                self._type_word(words[0], cap)
                self._last_commit = (words[0], cap, prev)
                self._last_auto = None
                self._note(words[0], prev)
                self._set_suggestions(words, mark=words[0])
                if self._shift == 1:
                    self._set_shift(0)
            self._trail_timeout = GLib.timeout_add(280, self._clear_trail)
        else:
            self._path = []
        self.canvas.queue_draw()
        return True

    def _activate(self, kid):
        if kid is None:
            return
        if kid == "SHIFT":
            if self._sys_caps:
                # Tap on the red CAPS badge releases the system Caps Lock
                # (a real keycode-58 press); our own Shift state is untouched.
                send([(KEY_CAPSLOCK, 1), (KEY_CAPSLOCK, 0)])
                self._sys_caps = False
                self.canvas.queue_draw()
            else:
                self._set_shift((self._shift + 1) % 3)
        elif kid == "BKSP":
            pass                        # fired on press
        elif kid == "SPACE":
            self._commit_space()
        elif kid == "ENTER":
            self._tap(KEYCODE["enter"])
        elif kid.startswith("GO:"):
            self._switch_screen(kid[3:])
        elif kid.startswith("K:"):
            self._tap(KEYCODE[kid[2:]])
        else:                           # literal character
            self._last_auto = None
            force = self._screen == "letters" and bool(self._shift)
            send(char_codes(kid, force_shift=force))
            self._sh_add(kid.upper() if force else kid)
            if self._buf:
                self._update_typing()
            else:
                self._set_suggestions([])
            if self._shift == 1:
                self._set_shift(0)

    def _switch_screen(self, name):
        self._screen = name
        self.keys = self._layout_cache[name]
        self.canvas.queue_draw()

    def _clear_trail(self):
        self._path = []
        self._trail_timeout = None
        self.canvas.queue_draw()
        return False

    def _replace_last(self, word):
        """Suggestion-bar tap after a swipe/autocorrect/plain word: swap the
        last committed word for this one, and learn it."""
        if not self._last_commit:
            return
        old, cap, prev = self._last_commit
        if word != old:
            send([(KEYCODE["bksp"], s)
                  for _ in range(len(old) + 1) for s in (1, 0)])
            self._sh_bksp(len(old) + 1)
            self._type_word(word, cap)
            self._last_commit = (word, cap, prev)
            if self.predictor.knows(old):
                self.usage.note(old, prev, n=-1)
            if self._last_auto and self._last_auto[1] == old:
                self.usage.reject(self._last_auto[0], old)
        self._last_auto = None
        self._learn(word)
        self._note(word, prev)
        self._set_suggestions([word], mark=word)

    # ----- tap-typing prediction / autocorrect -----

    def _poll_caps(self):
        on = False
        if self._caps_led:
            try:
                with open(self._caps_led) as f:
                    on = f.read().strip() == "1"
            except OSError:
                pass
        if on != self._sys_caps:
            self._sys_caps = on
            sys.stderr.write("%s system caps lock %s\n" % (
                time.strftime("%Y-%m-%d %H:%M:%S"), "ON" if on else "off"))
            sys.stderr.flush()
            self.canvas.queue_draw()
        return True

    def _set_shift(self, v):
        self._shift = v
        if hasattr(self, "_tab_btn"):
            self._tab_btn.set_label("\u21e4 tab" if v else "tab")
        self.canvas.queue_draw()

    @property
    def _buf(self):
        """The word being typed: the alphabetic tail of our typed text."""
        i = len(self._shadow)
        while i and self._shadow[i - 1].isalpha():
            i -= 1
        return self._shadow[i:]

    def _prev_word(self):
        """Word before the one being typed, if only spaces separate them
        (punctuation/newline = new sentence = no context)."""
        t = self._shadow[:len(self._shadow) - len(self._buf)].rstrip(" ")
        i = len(t)
        while i and t[i - 1].isalpha():
            i -= 1
        return t[i:].lower() or None

    def _sh_add(self, text):
        self._shadow = (self._shadow + text)[-SHADOW_MAX:]

    def _sh_bksp(self, n=1):
        self._shadow = self._shadow[:-n] if n < len(self._shadow) else ""

    def _type_word(self, word, cap):
        type_word(word, capitalize=cap)
        self._sh_add((word[:1].upper() + word[1:] if cap else word) + " ")

    def _reset_word(self):
        self._shadow = ""
        self._last_auto = None
        self._set_suggestions([])

    def _learn(self, word):
        if self.predictor.learn(word):
            if all(c in self.centers for c in word):
                self.decoder.index.setdefault((word[0], word[-1]),
                                              []).append((word, 300))
            print("learned: %s" % word, flush=True)

    def _note(self, word, prev):
        """Count a committed word (and the pair) toward ranking. Only real
        words: random strings (passwords) never get stored."""
        word = word.lower()
        if not word.isalpha() or not self.predictor.valid(word):
            return
        if not self.predictor.knows(word):
            self._learn(word)           # hunspell-valid but not in list
        if prev and not self.predictor.knows(prev):
            prev = None                 # never store an unknown word as context
        self.usage.note(word, prev)
        if not self._save_timer:
            self._save_timer = GLib.timeout_add_seconds(15, self._save_usage)

    def _save_usage(self):
        self._save_timer = None
        try:
            self.usage.save()
        except OSError as e:
            print("usage save failed: %s" % e, flush=True)
        return False

    def _on_term(self):
        self._save_usage()
        Gtk.main_quit()
        return False

    def _update_typing(self):
        self._set_suggestions(
            self.predictor.complete(self._buf.lower(), self._prev_word()),
            action=self._commit_typed)

    def _show_next(self):
        """After a word + space: what you usually type next."""
        nxt = self.predictor.next_words(self._prev_word())
        self._set_suggestions(nxt, action=self._commit_typed)

    def _commit_typed(self, word):
        buf, prev = self._buf, self._prev_word()
        cap = buf[:1].isupper()
        self._last_auto = None
        if buf and word.startswith(buf.lower()):
            codes = []
            for ch in word[len(buf):]:
                codes += char_codes(ch)
            codes += [(KEYCODE["space"], 1), (KEYCODE["space"], 0)]
            send(codes)
            self._sh_add(word[len(buf):] + " ")
        else:
            send([(KEYCODE["bksp"], s) for _ in buf for s in (1, 0)])
            self._sh_bksp(len(buf))
            self._type_word(word, cap)
        self._last_commit = (word, cap, prev)
        self._note(word, prev)
        self._show_next()

    def _commit_space(self):
        self._poke()
        raw, prev = self._buf, self._prev_word()
        buf, cap = raw.lower(), raw[:1].isupper()
        self._last_auto = None
        plain = [(KEYCODE["space"], 1), (KEYCODE["space"], 0)]
        if not buf:
            send(plain)
            self._sh_add(" ")
            self._set_suggestions([])
            return
        if (len(buf) < 3 or self.predictor.knows(buf)
                or self.predictor.valid(buf)):
            send(plain)
            self._sh_add(" ")
            self._last_commit = (buf, cap, prev)
            self._note(buf, prev)
            self._show_next()
            return
        cands = self.predictor.correct(buf, prev)
        # auto-replace only when it's a clear win: 4+ letters (3-letter
        # "fixes" like ssh->ash were mostly wrong) and no near-tie between
        # candidates (workd: work/world/worked all score close — suggest,
        # don't guess)
        if (cands and cands[0][0] <= AUTOCORRECT_MAX and len(buf) >= 4
                and (len(cands) == 1
                     or cands[1][0] - cands[0][0] >= 0.20)):
            corr = cands[0][1]
            send([(KEYCODE["bksp"], s) for _ in buf for s in (1, 0)])
            self._sh_bksp(len(buf))
            self._type_word(corr, cap)
            self._last_commit = (corr, cap, prev)
            self._last_auto = (buf, corr)
            self._note(corr, prev)
            print("autocorrect: %s -> %s (%.2f)" % (buf, corr, cands[0][0]),
                  flush=True)
            self._set_suggestions([buf] + [w for _s, w in cands[:3]],
                                  mark=corr)
        else:
            # unknown word kept as typed: offer it in the bar so one tap
            # teaches it (never auto-learned: could be a password)
            send(plain)
            self._sh_add(" ")
            self._last_commit = (buf, cap, prev)
            self._set_suggestions([buf] + [w for _s, w in cands[:3]],
                                  add=buf)

    def _undo_autocorrect(self):
        """Backspace right after an autocorrect restores what you typed and
        never makes that correction again."""
        if not self._last_auto:
            return False
        typed, corr = self._last_auto
        self._last_auto = None
        tail = self._shadow[-(len(corr) + 1):].lower()
        if tail != corr + " ":
            return False
        _w, cap, prev = self._last_commit
        send([(KEYCODE["bksp"], s) for _ in range(len(corr) + 1)
              for s in (1, 0)])
        self._sh_bksp(len(corr) + 1)
        codes = []
        for i, ch in enumerate(typed):
            codes += char_codes(ch, force_shift=(cap and i == 0))
        send(codes)
        self._sh_add(typed[:1].upper() + typed[1:] if cap else typed)
        self.usage.reject(typed, corr)
        self.usage.note(corr, prev, n=-1)
        self._learn(typed)
        print("undo autocorrect: %s -> %s" % (corr, typed), flush=True)
        self._update_typing()
        return True

    # ----- shared behaviour -----

    def _tap(self, code):
        self._poke()
        if code == KEYCODE["bksp"]:
            self._last_bksp = time.monotonic()
            self._last_auto = None
            self._sh_bksp()
            if self._buf:
                self._update_typing()
            else:
                self._set_suggestions([])
        else:
            if code == KEYCODE["enter"] and self._buf:
                self._note(self._buf, self._prev_word())
            self._reset_word()
        if self._shift and code in SHIFTABLE:
            send([(SHIFT, 1), (code, 1), (code, 0), (SHIFT, 0)])
            if self._shift == 1:
                self._set_shift(0)
        else:
            send([(code, 1), (code, 0)])

    def _combo_key(self, code):
        """ctrl(+shift on armed Shift)+key; Shift consumed like on nav keys."""
        self._poke()
        self._reset_word()
        if self._shift:
            send([(KEYCODE["ctrl"], 1), (SHIFT, 1), (code, 1), (code, 0),
                  (SHIFT, 0), (KEYCODE["ctrl"], 0)])
            if self._shift == 1:
                self._set_shift(0)
        else:
            send([(KEYCODE["ctrl"], 1), (code, 1), (code, 0),
                  (KEYCODE["ctrl"], 0)])

    def _copy(self, *_):
        self._combo_key(KEYCODE["c"])

    def _paste(self, *_):
        self._combo_key(KEYCODE["v"])

    # ----- speech to text -----

    def _mic_toggle(self, _b):
        self._poke()
        if self._rec_proc is None and not self._transcribing:
            os.makedirs(os.path.dirname(MIC_WAV), exist_ok=True)
            try:
                self._rec_proc = subprocess.Popen(
                    ["pw-record", "--rate", "16000", "--channels", "1",
                     MIC_WAV])
            except OSError as e:
                print("mic: pw-record failed: %s" % e, flush=True)
                return
            self._set_mic_label("◉ stop", rec=True)
            # don't auto-collapse mid-recording: the stop button would vanish
            if self._idle_timer:
                GLib.source_remove(self._idle_timer)
                self._idle_timer = None
        elif self._rec_proc is not None:
            p, self._rec_proc = self._rec_proc, None
            p.terminate()
            try:
                p.wait(2)
            except subprocess.TimeoutExpired:
                p.kill()
                p.wait()
            self._transcribing = True
            self._set_mic_label("…")
            threading.Thread(target=self._transcribe, daemon=True).start()

    def _transcribe(self):
        global _WHISPER
        text = ""
        try:
            if _WHISPER is None:
                os.environ.setdefault("HF_HUB_OFFLINE", "1")  # model is cached
                from faster_whisper import WhisperModel
                _WHISPER = WhisperModel("base.en", device="cpu",
                                        compute_type="int8", cpu_threads=4)
            segs, _info = _WHISPER.transcribe(
                MIC_WAV, beam_size=5, language="en",
                condition_on_previous_text=False,
                initial_prompt="Claude Code terminal commands on a Fedora "
                               "Surface Go tablet: keyboard, touchscreen, "
                               "mouse pointer, copy, paste, drag, select.")
            text = "".join(s.text for s in segs).strip()
        except Exception as e:
            print("mic: transcribe failed: %r" % e, flush=True)
        GLib.idle_add(self._mic_done, text)

    def _mic_done(self, text):
        self._transcribing = False
        self._set_mic_label("🎤")
        if text:
            print("mic: %r" % text, flush=True)
            type_text(text + " ")
            self._last_auto = None
            self._sh_add(text + " ")
            self._set_suggestions([])
        else:
            self._set_suggestions(["(no speech)"], action=lambda _w: None)
        self._poke()
        return False

    def _press_repeat(self, _b, code):
        self._tap(code)
        self._stop_repeat()
        self._timer = GLib.timeout_add(REPEAT_DELAY, self._begin_repeat, code)

    def _begin_repeat(self, code):
        self._timer = GLib.timeout_add(REPEAT_MS,
                                       lambda: (self._tap(code), True)[1])
        return False

    def _stop_repeat(self, *_):
        if self._timer:
            GLib.source_remove(self._timer)
            self._timer = None

    def _poke(self):
        if self._idle_timer:
            GLib.source_remove(self._idle_timer)
        self._idle_timer = GLib.timeout_add_seconds(IDLE_S, self._idle_collapse)

    def _idle_collapse(self):
        self._idle_timer = None
        if self.stack.get_visible_child_name() == "body":
            self._collapse()
        return False

    def _expand(self, *_):
        self.stack.set_visible_child_name("body")
        self._switch_screen("letters")
        self._reset_word()
        self._poke()

    def _collapse(self, *_):
        if self._idle_timer:
            GLib.source_remove(self._idle_timer)
            self._idle_timer = None
        self._mouse_teardown()
        self.stack.set_visible_child_name("pill")
        self.resize(self.mon.width, 1)

    def _dock(self, *_):
        w, h = self.get_size()
        self.move(self.mon.x, self.mon.y + self.mon.height - h)
        # Reserve the space we occupy so maximized windows resize above us
        # and the focused input box stays visible -- pill included: it is
        # keep-above, so an unreserved strip under it hides bottom-of-screen
        # UI (status lines, accept-edits bars).
        self._set_strut(h)

    def _set_strut(self, px):
        """Publish _NET_WM_STRUT_PARTIAL via libX11; Gdk.property_change
        is not exposed by this build's introspection data."""
        gw = self.get_window()
        if not gw or px == getattr(self, "_strut", None):
            return
        if not hasattr(self, "_xlib"):
            lib = ctypes.util.find_library("X11")
            self._xlib = ctypes.CDLL(lib) if lib else None
            if self._xlib:
                self._xlib.XOpenDisplay.restype = ctypes.c_void_p
                self._xlib.XInternAtom.restype = ctypes.c_ulong
                self._xlib.XInternAtom.argtypes = [ctypes.c_void_p,
                                                   ctypes.c_char_p,
                                                   ctypes.c_int]
                self._xlib.XChangeProperty.argtypes = [
                    ctypes.c_void_p, ctypes.c_ulong, ctypes.c_ulong,
                    ctypes.c_ulong, ctypes.c_int, ctypes.c_int,
                    ctypes.c_void_p, ctypes.c_int]
                self._xlib.XFlush.argtypes = [ctypes.c_void_p]
                self._xlib.XDisplayHeight.argtypes = [ctypes.c_void_p, ctypes.c_int]
                self._xlib.XDisplayWidth.argtypes = [ctypes.c_void_p, ctypes.c_int]
                self._xdpy = self._xlib.XOpenDisplay(None)
        if not self._xlib or not self._xdpy:
            return
        self._strut = px
        xid = gw.get_xid()
        # Xwayland's root is the PHYSICAL panel size while GDK speaks
        # logical pixels; struts are read in X11 coords, so scale up.
        rw = self._xlib.XDisplayWidth(self._xdpy, 0)
        rh = self._xlib.XDisplayHeight(self._xdpy, 0)
        sx = px * rh // self.mon.height
        print("strut -> %d logical / %d x11 (root %dx%d)" % (px, sx, rw, rh),
              flush=True)
        vals = [0, 0, 0, sx, 0, 0, 0, 0, 0, 0, 0, rw - 1]
        arr12 = (ctypes.c_ulong * 12)(*vals)
        arr4 = (ctypes.c_ulong * 4)(*vals[:4])
        cardinal = self._xlib.XInternAtom(self._xdpy, b"CARDINAL", 0)
        for name, arr, n in (
                (b"_NET_WM_STRUT_PARTIAL", arr12, 12),
                (b"_NET_WM_STRUT", arr4, 4)):
            atom = self._xlib.XInternAtom(self._xdpy, name, 0)
            self._xlib.XChangeProperty(self._xdpy, xid, atom, cardinal,
                                       32, 0, arr, n)   # 0 = PropModeReplace
        self._xlib.XFlush(self._xdpy)

    def _reassert(self):
        win = self.get_window()
        if win:
            self.set_keep_above(True)
            win.raise_()
        return True


def selftest():
    kb = Keyboard.__new__(Keyboard)
    kb.mon = type("m", (), {"width": 720})()
    kb.key_w, kb.key_h = 72.0, 48
    layout = []
    kb._layout_cache = {}
    kb._compute_layout.__func__ if False else None
    keys = Keyboard._compute_layout(kb, "letters")
    centers = {kid: (x + w / 2, y + h / 2) for kid, x, y, w, h, _l in keys
               if len(kid) == 1 and kid.isalpha()}
    dec = Decoder(centers)
    n = sum(len(v) for v in dec.index.values())
    print("dict size:", n)
    ok = 0
    tests = sys.argv[2:] or ["hello", "the", "keyboard", "work", "chrome",
                             "swipe", "screen", "delete"]
    for word in tests:
        path = [centers[c] for c in word]
        got = dec.decode(path, kb.key_w)
        good = got and got[0] == word
        ok += bool(good)
        print("%-10s -> %s %s" % (word, got[:3], "OK" if good else "miss"))
    print("%d/%d top-1" % (ok, len(tests)))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        selftest()
        sys.exit(0)
    if not GLib.find_program_in_path("ydotool"):
        sys.exit("ydotool missing")
    if not os.path.exists(SOCKET):
        sys.exit("ydotoold socket missing at %s" % SOCKET)
    # Early-login race: as the first X11 client we can connect before
    # mutter publishes the scale-2 xsettings, so GDK reads the physical
    # 2160x1440 root as scale-1 logical and the dock lands off-screen
    # (and never hears about the scale afterwards). Re-exec -- a fresh
    # process rereads xsettings -- until the scale appears; capped so a
    # genuine scale-1 setup still launches after ~30s.
    _m = Gdk.Display.get_default().get_monitor(0)
    if (_m.get_scale_factor() == 1
            and max(_m.get_geometry().width, _m.get_geometry().height) >= 1600):
        _tries = int(os.environ.get("TOUCHKBD_SCALE_RETRY", "0"))
        if _tries < 15:
            os.environ["TOUCHKBD_SCALE_RETRY"] = str(_tries + 1)
            print("scale not ready (try %d), re-exec in 2s" % _tries,
                  flush=True)
            time.sleep(2)
            os.execv(sys.executable,
                     [sys.executable, os.path.abspath(__file__)])
        print("scale never appeared; launching unscaled", flush=True)
    kb = Keyboard()
    kb.show_all()
    kb._collapse()
    Gtk.main()
