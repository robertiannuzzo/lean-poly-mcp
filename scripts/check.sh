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
for f in test/PolyTest.lean test/McpTest.lean; do
  out=$(lake env lean "$f" 2>&1)
  if [ -z "$out" ]; then echo "ok    $f"; else echo "FAIL  $f"; echo "$out" | head -20; fail=1; fi
done

# Self-checking suite: exits non-zero and reports which case broke.
if lake env lean --run test/OracleTest.lean; then :; else fail=1; fi

if [ "${1:-}" = "--full" ]; then
  echo "--- Mathlib suite (~70s) ---"
  if lake env lean --run test/MathlibOracleTest.lean; then :; else fail=1; fi
fi

[ "$fail" = 0 ] && echo "ALL PASS" || echo "FAILURES ABOVE"
exit $fail
