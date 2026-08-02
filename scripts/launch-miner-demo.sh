#!/usr/bin/env bash
# Launch the local Mathlib statement miner demo and open it in the browser.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PORT="${PORT:-8770}"
URL="http://localhost:${PORT}"

cd "$ROOT"

if curl -fsS "${URL}/" >/dev/null 2>&1; then
  echo "Mathlib Statement Miner is already running at ${URL}"
  open "$URL"
  exit 0
fi

echo "Building miner-report..."
if ! build_out=$(lake build miner-report 2>&1); then
  echo "$build_out" | grep -E '^(error|✖)|\.lean:' | head -40
  exit 1
fi

echo "Starting Mathlib Statement Miner at ${URL}"
PORT="$PORT" python3 web/serve.py &
server_pid=$!

cleanup() {
  kill "$server_pid" 2>/dev/null || true
}
trap cleanup EXIT

for _ in $(seq 1 60); do
  if curl -fsS "${URL}/" >/dev/null 2>&1; then
    open "$URL"
    echo
    echo "Demo is running at ${URL}"
    echo "Leave this window open while presenting. Press Ctrl-C to stop."
    wait "$server_pid"
    exit $?
  fi
  if ! kill -0 "$server_pid" 2>/dev/null; then
    echo "Server exited before it became ready."
    wait "$server_pid"
    exit $?
  fi
  sleep 1
done

echo "Timed out waiting for ${URL}"
exit 1
