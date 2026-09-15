#!/bin/bash
# Run as root: sudo bash setup-ydotoold.sh [uid]
# Points the shipped ydotool.service at a socket inside /run/user/<uid>,
# which is mode 0700 and owned by that user -- so a world-readable socket
# in there is still reachable only by that user and root.
set -e
uid="${1:-${SUDO_UID:-1000}}"
d=/etc/systemd/system/ydotool.service.d
mkdir -p "$d"
cat > "$d/override.conf" <<CONF
[Unit]
After=user-runtime-dir@${uid}.service
Wants=user-runtime-dir@${uid}.service

[Service]
ExecStart=
ExecStart=/usr/bin/ydotoold --socket-path /run/user/${uid}/.ydotool_socket --socket-perm 0666
RestartSec=2
CONF
systemctl daemon-reload
systemctl enable --now ydotool.service
sleep 1
systemctl --no-pager --lines=5 status ydotool.service || true
ls -l "/run/user/${uid}/.ydotool_socket"
