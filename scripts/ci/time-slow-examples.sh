#!/usr/bin/env bash
# Measure each H109 slow example module on one core (`LEAN_NUM_THREADS=1`), as the CI
# `slow-examples` jobs build them. Builds the slow library first (fetching what Lake's
# cache has), then re-elaborates every module listed in SoliditySlowExamples.lean with
# `lake lean`, which ignores the artifact cache, so each figure is that module's own
# cold elaboration time with its imports already built.
# Usage: scripts/ci/time-slow-examples.sh [MODULE...]   (default: every slow module)
# Prints "<seconds>\t<module>\t<exit status>" per module, slowest first, on stdout.
set -uo pipefail
root=$(git rev-parse --show-toplevel) || exit 2
cd "$root" || exit 2
export PATH="$HOME/.elan/bin:$PATH"
if [ $# -gt 0 ]; then mods=("$@"); else
  mapfile -t mods < <(sed -n 's/^import \(Solidity\.[A-Za-z0-9_.]*\).*/\1/p' SoliditySlowExamples.lean)
fi
[ ${#mods[@]} -gt 0 ] || { echo "time-slow-examples: no modules" >&2; exit 2; }
lake build SoliditySlowExamples >&2 || { echo "time-slow-examples: build failed" >&2; exit 1; }
out=$(mktemp)
for m in "${mods[@]}"; do
  f=${m//.//}.lean
  [ -f "$f" ] || { echo "time-slow-examples: no file $f" >&2; exit 2; }
  start=$(date +%s.%N)
  LEAN_NUM_THREADS=1 lake lean "$f" -- --tstack=131072 >/dev/null 2>&1; st=$?
  end=$(date +%s.%N)
  printf '%.1f\t%s\t%s\n' "$(echo "$end - $start" | bc)" "$m" "$st" | tee -a "$out" >&2
done
sort -rn "$out"; rm -f "$out"
