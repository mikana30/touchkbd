# touchkbd

A swipe-typeable on-screen keyboard for Linux tablets that types into
**every** app — including the ones GNOME's native OSK can't reach — plus
offline speech-to-text on a mic key.

Built for a Microsoft Surface Go running Fedora/GNOME (Wayland), but nothing
in it is Surface-specific: it's a single-file GTK3 app that injects real
keystrokes at the uinput layer via [ydotool](https://github.com/ReimuNotMoe/ydotool),
so anything that accepts a physical keyboard accepts this.

## Why it exists

GNOME's native OSK never appears for Chrome on Wayland (the text-input
protocol traffic is correct — verified with `WAYLAND_DEBUG=1` — but the
shell never shows the keyboard; Firefox with identical traffic works).
Rather than fight that shell-side bug, this keyboard sidesteps the whole
input-method stack: it's a dock window that sends key events through
`/dev/uinput`, exactly like a USB keyboard. Focus decides where the
keys go, and every toolkit, terminal, and browser just works.

## Features

- **Swipe typing** — SHARK2-style decoder (DTW over location + shape
  channels, endpoint anchoring, corner counting) against a 10k frequency
  wordlist plus a personal dictionary that learns words you teach it.
- **Tap typing help** — prefix completions and a deliberately conservative
  one-edit autocorrect (adjacent-key and transposition typos are cheap,
  anything else must be a very common word — this keyboard mostly types
  into terminals, where "correcting" `grep` would be unforgivable).
  Autocorrects are shown in the suggestion bar; tap the original to revert
  *and* learn it.
- **Speech-to-text** — a 🎤 key records the mic (PipeWire `pw-record`) and
  transcribes locally with [faster-whisper](https://github.com/SYSTRAN/faster-whisper)
  `base.en` int8. Fully offline, usable even on a Pentium-class tablet
  (~realtime transcription; first use loads the model for a few seconds).
- **Three screens** (letters / ?123 / #+=), Gboard-ish layout, and a
  utility row: esc, tab, delete, page up/down, arrows, hide.
- **Terminal-friendly details** — on-screen Shift applies to tab/enter/
  arrows (shift+tab reaches menu cyclers), arrow-Up sits at the far right
  edge where a missed spacebar tap can't recall shell history.
- **Stays out of the way** — collapses to a bottom-edge pill (with scroll
  keys) after 20s idle; publishes X11 struts so maximized windows resize
  above it and the focused input box stays visible; auto-relaunches on
  screen rotation.

## Requirements

- GTK3 + PyGObject (`python3-gobject`, `gtk3`)
- `ydotool`/`ydotoold` (uinput injection)
- `pw-record` (PipeWire, for the mic key) and `pip install faster-whisper`
- An X11-capable session for the dock window (Xwayland is fine — the
  keyboard itself runs as an X11 client; the keys it types are
  compositor-agnostic)

## Install

```sh
# 1. ydotoold as a system service with a user-reachable socket
sudo bash setup-ydotoold.sh          # or setup-ydotoold.sh <your-uid>

# 2. wordlist + keyboard
mkdir -p ~/.local/share/touchkbd
cp words.txt ~/.local/share/touchkbd/
./touchkbd.py                        # or bash tk-restart.sh

# 3. optional: speech-to-text
python3 -m pip install --user faster-whisper   # model auto-downloads on first use

# 4. optional (GNOME): stop the native OSK from popping up over this one
cp -r gnome-extension/no-auto-osk@touchkbd ~/.local/share/gnome-shell/extensions/
# log out/in, then:
gnome-extensions enable no-auto-osk@touchkbd
```

Autostart it however you like (a `.desktop` file in `~/.config/autostart`
works). At login the keyboard handles the race where it starts before the
compositor publishes the HiDPI scale.

Run `./touchkbd.py --test` for a quick offline check of the swipe decoder.

## Notes & caveats

- Keystrokes go to whatever has focus, like a hardware keyboard. That is
  the feature.
- Struts are published in physical pixels (Xwayland's root is unscaled);
  the code handles the logical→physical conversion.
- The swipe decoder, autocorrect thresholds, and layout are all in one
  readable Python file — tune to taste.
- `words.txt` is [google-10000-english](https://github.com/first20hours/google-10000-english)
  (derived from the Google Trillion Word Corpus).
- Personal dictionary lives at `~/.local/share/touchkbd/user-words.txt`,
  one word per line.

## License

MIT
