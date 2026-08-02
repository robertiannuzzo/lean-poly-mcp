#!/usr/bin/env bash
# Compact test sweep: one line per suite, detail only on failure.
#   ./scripts/check.sh          fast suites (Init-only), seconds
#   ./scripts/check.sh --full   adds the Mathlib suite, ~70s
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

build_out=$(lake build 2>&1 | grep -E '^(error|✖)|\.lean:' | head -20)
if [ -n "$build_out" ]; then echo "FAIL  build"; echo "$build_out"; exit 1; fi
echo "ok    build"

# Typecheck-only suites: any output at all is a failure.
for f in test/PolyTest.lean test/McpTest.lean docs/tactic-notes.lean; do
  out=$(lake env lean "$f" 2>&1)
  if [ -z "$out" ]; then echo "ok    $f"; else echo "FAIL  $f"; echo "$out" | head -20; fail=1; fi
done

# Self-checking suite: exits non-zero and reports which case broke.
if lake env lean --run test/OracleTest.lean; then :; else fail=1; fi

# Offline by construction: replays recorded Aristotle output, but re-runs the real
# oracle. Never touches the network, so it belongs in the fast path.
if lake env lean --run test/AristotleTest.lean; then :; else fail=1; fi

if [ "${1:-}" = "--full" ]; then
  echo "--- Mathlib suite (~70s) ---"
  if lake env lean --run test/MathlibOracleTest.lean; then :; else fail=1; fi
  echo "--- benchmark: how far the free ladder gets (~70s) ---"
  if lake env lean --run test/BenchmarkTest.lean; then :; else fail=1; fi
  echo "--- agent runs (~50s) ---"
  if lake env lean --run test/AgentTest.lean; then :; else fail=1; fi
fi

[ "$fail" = 0 ] && echo "ALL PASS" || echo "FAILURES ABOVE"
exit $fail
