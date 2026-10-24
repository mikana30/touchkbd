#!/usr/bin/env python3
"""Whisper transcription for the Surface Go on-screen keyboard (touchkbd).

The Go's Pentium needs ~5s per clip; this runs the same base.en model on
uriel in ~1s. Tailnet only: binds to uriel's tailscale address.

POST /transcribe   body = raw s16le 16 kHz mono PCM
  headers: X-Prompt (percent-encoded initial prompt), X-Beam (int)
  -> {"text": "...", "segments": [[start_s, end_s, sentence, mean_word_prob], ...], "ms": 812}
GET /health -> {"ok": true, "model": "base.en"}
"""
import json, os, re, threading, time, urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import numpy as np
from faster_whisper import WhisperModel

BIND = os.environ.get("TKW_BIND", "100.116.82.95")
PORT = int(os.environ.get("TKW_PORT", "8791"))
MODEL = os.environ.get("TKW_MODEL", "base.en")
THREADS = int(os.environ.get("TKW_THREADS", "4"))  # 4 cores; 8 HT was slower
MAX_BYTES = 16000 * 2 * 120                          # 2 minutes

model = WhisperModel(MODEL, device="cpu", compute_type="int8",
                     cpu_threads=THREADS)
lock = threading.Lock()


# Whisper invents these from silence or noise (YouTube-subtitle training
# data). A sentence matching one is dropped.
HALLUCINATIONS = re.compile(
    r"thanks? (you )?(so |very )?much for watching|thanks? (you )?for watching"
    r"|see you (guys )?(in the )?next (video|time|one)|like and subscribe"
    r"|please subscribe|don't forget to subscribe|subtitles? by"
    r"|captions? by|transcribed by|amara\.org", re.I)


def drop_hallucinations(sents):
    return [s for s in sents if not HALLUCINATIONS.search(s[2])]


def sentences(segs):
    """Whisper segments (with .words) -> [[start, end, text]] per sentence,
    split after words ending in . ? or !"""
    out, cur = [], []
    for s in segs:
        for w in (s.words or []):
            cur.append(w)
            if w.word.strip().endswith((".", "?", "!")):
                out.append(cur)
                cur = []
    if cur:
        out.append(cur)
    return [[round(ws[0].start, 2), round(ws[-1].end, 2),
             "".join(w.word for w in ws).strip(),
             round(sum(w.probability for w in ws) / len(ws), 2)] for ws in out]


class H(BaseHTTPRequestHandler):
    def _json(self, code, obj):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path == "/health":
            self._json(200, {"ok": True, "model": MODEL})
        else:
            self._json(404, {"error": "not found"})

    def do_POST(self):
        if self.path != "/transcribe":
            return self._json(404, {"error": "not found"})
        n = int(self.headers.get("Content-Length", 0))
        if not 0 < n <= MAX_BYTES:
            return self._json(400, {"error": "bad length"})
        pcm = self.rfile.read(n)
        audio = np.frombuffer(pcm[:n - n % 2], dtype=np.int16)
        audio = audio.astype(np.float32) / 32768.0
        prompt = urllib.parse.unquote(self.headers.get("X-Prompt", "")) or None
        beam = max(1, min(5, int(self.headers.get("X-Beam", "5"))))
        t = time.monotonic()
        try:
            with lock:
                segs, _i = model.transcribe(
                    audio, language="en", beam_size=beam, vad_filter=True,
                    condition_on_previous_text=False,
                    temperature=0.0, initial_prompt=prompt,
                    word_timestamps=True)
                segs = drop_hallucinations(sentences(segs))
                text = " ".join(s[2] for s in segs).strip()
        except Exception as e:
            return self._json(500, {"error": repr(e)})
        ms = int((time.monotonic() - t) * 1000)
        print("%.1fs audio -> %dms %r" % (len(audio) / 16000, ms, text[:60]),
              flush=True)
        self._json(200, {"text": text, "segments": segs, "ms": ms})

    def log_message(self, *_a):
        pass


if __name__ == "__main__":
    print("tk-whisper: %s on %s:%d" % (MODEL, BIND, PORT), flush=True)
    ThreadingHTTPServer((BIND, PORT), H).serve_forever()
