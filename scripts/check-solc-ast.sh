#!/usr/bin/env bash
# Check the solc fixture `tests/solc/TestSuite.ast.json` (scripts/solc-ast.mjs):
# regenerate it from the solkey checkout with the pinned soljson and diff, and
# compare it with solkey's own cached solc output where there is one. Then check
# that the importing module names the fixture's hash.
#
# Usage: scripts/check-solc-ast.sh [--solkey <checkout>]
# Exit 0 = the fixture is what the compiler writes, 1 = it drifted (re-pin with
# `node scripts/solc-ast.mjs`).
set -euo pipefail

cd "$(dirname "$0")/.."
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

status=0
# one compile: the run prints the hash of what it wrote, and exits 1 (after
# printing it) when solkey's cached output differs
out="$(node scripts/solc-ast.mjs --no-wrapper --compare-cache --out "$scratch/TestSuite.ast.json" "$@" 2>&1)" || status=1
printf '%s\n' "$out"
if ! diff -q tests/solc/TestSuite.ast.json "$scratch/TestSuite.ast.json" >/dev/null; then
  diff -u tests/solc/TestSuite.ast.json "$scratch/TestSuite.ast.json" | head -40
  echo "check-solc-ast: the fixture drifted (re-pin with node scripts/solc-ast.mjs)"
  status=1
fi
hash="$(printf '%s\n' "$out" | sed -n 's/.*hash \(0x[0-9a-f]*\).*/\1/p')"
if [ -z "$hash" ] || ! grep -q "hash $hash" Solidity/Solkey/TestSuite.lean; then
  echo "check-solc-ast: Solidity/Solkey/TestSuite.lean does not name the fixture's hash $hash"
  status=1
fi
if [ "$status" = 0 ]; then echo "check-solc-ast: ok"; else echo "check-solc-ast: failed"; fi
exit "$status"
