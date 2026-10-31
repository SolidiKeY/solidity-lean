#!/usr/bin/env bash
set -euo pipefail
out=${1:?absolute evidence directory required}
for file in Solidity/Backend/InternalFlow/*.lean; do
  name=$(basename "$file" .lean)
  echo "lake env lean -j1 --tstack=131072 $file"
  lake env lean -j1 --tstack=131072 "$file" > "$out/final-$name-diagnostics.log" 2>&1
done
