#!/bin/bash
# (Re)start touchkbd, logging to ~/.local/share/touchkbd/touchkbd.log.
LOG="$HOME/.local/share/touchkbd/touchkbd.log"
mkdir -p "$(dirname "$LOG")"
# match both "python3 ..." and "/usr/bin/python3 ..." command lines
pkill -f 'python3 .*touch''kbd\.py'
sleep 1
cd "$HOME"
setsid nohup "$(dirname "$(readlink -f "$0")")/touchkbd.py" > "$LOG" 2>&1 < /dev/null &
sleep 3
pgrep -af 'python3 .*touch''kbd\.py' | cut -c1-80
cat "$LOG"
