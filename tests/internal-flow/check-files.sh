#!/usr/bin/env bash
set -euo pipefail
out=${1:?absolute evidence directory required}
for file in Solidity/Backend/InternalFlow/*.lean; do
  name=$(basename "$file" .lean)
  echo "lake env lean -j1 --tstack=131072 $file"
  lake env lean -j1 --tstack=131072 "$file" > "$out/final-$name-diagnostics.log" 2>&1
done

# Freshly check the added metadata tool as well; every original check remains.
file=tests/internal-flow/AxiomReports.lean
echo "lake env lean -j1 --tstack=131072 $file"
lake env lean -j1 --tstack=131072 "$file" > "$out/final-AxiomReports-diagnostics.log" 2>&1

file=tests/internal-flow/PublishedMemoryCalls.lean
echo "lake env lean -j1 --tstack=131072 $file"
lake env lean -j1 --tstack=131072 "$file" > "$out/final-PublishedMemoryCalls-diagnostics.log" 2>&1

file=tests/internal-flow/MutatingMemoryCalls.lean
echo "lake env lean -j1 --tstack=131072 $file"
lake env lean -j1 --tstack=131072 "$file" > "$out/final-MutatingMemoryCalls-diagnostics.log" 2>&1

file=tests/internal-flow/TupleMemoryCalls.lean
echo "lake env lean -j1 --tstack=131072 $file"
lake env lean -j1 --tstack=131072 "$file" > "$out/final-TupleMemoryCalls-diagnostics.log" 2>&1
