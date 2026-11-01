#!/usr/bin/env bash
# Lane CF1: replay the ABI entry-decoding fixtures one by one through the
# upstream runner (exact path filter, batch size 1, distinct output
# directory per fixture). Usage: scripts/abi-entry-fixtures.sh COMPILER LABEL
# Reports land in .lake/upstream/cf1-LABEL/<n>/results.json; collect them with
# scripts/abi-entry-collect.py. Fixture list: tests/upstream/cf1-abi-entry-fixtures.txt.
set -uo pipefail
compiler="$1"; label="$2"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
n=0
while IFS= read -r path; do
  [[ -z "$path" || "$path" == \#* ]] && continue
  n=$((n+1))
  out=".lake/upstream/cf1-$label/$n"; mkdir -p ".lake/upstream/cf1-$label"
  start=$(date +%s%3N)
  node scripts/solidity-upstream.mjs run --compiler "$compiler" \
    --filter "test/libsolidity/semanticTests/$path" --batch-size 1 --out "$out" > "$out.log" 2>&1
  code=$?
  echo "$n $path exit=$code ms=$(( $(date +%s%3N) - start ))"
done < tests/upstream/cf1-abi-entry-fixtures.txt
