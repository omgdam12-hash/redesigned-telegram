#!/bin/bash
# Web terminal gateway used by ttyd. One shared public terminal port asks
# for a one-time code (generated per-SSH-request by the Discord bot) and,
# if valid and unexpired, execs into that VPS's Linux user shell.
set -u

DB_PATH="${VPS_DB_PATH:-vps.db}"

echo "==================================================="
echo " DevilClouds VM 2 Web Terminal Gateway"
echo "==================================================="
read -p "Enter your one-time access code: " CODE

if [ -z "$CODE" ]; then
    echo "No code entered. Disconnecting."
    sleep 2
    exit 1
fi

NOW=$(date +%s)
TARGET=$(sqlite3 "$DB_PATH" "SELECT container_name FROM access_codes WHERE code='$CODE' AND expires_at > $NOW;" 2>/dev/null)

if [ -z "$TARGET" ]; then
    echo "Invalid or expired code."
    sleep 2
    exit 1
fi

# One-time use - burn the code immediately so it can't be reused/shared
sqlite3 "$DB_PATH" "DELETE FROM access_codes WHERE code='$CODE';" 2>/dev/null

if ! id -u "$TARGET" >/dev/null 2>&1; then
    echo "VPS account '$TARGET' no longer exists."
    sleep 2
    exit 1
fi

echo "Access granted. Connecting to $TARGET ..."
sleep 1
exec su - "$TARGET"
