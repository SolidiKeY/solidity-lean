#!/usr/bin/env bash
set -uo pipefail
[ $# -ge 2 ] || { echo "usage: try-tactics.sh MODULE GOAL [CANDIDATE...]" >&2; exit 2; }
module=$1; goal=$2; shift 2
if [ -f "$goal" ]; then proposition=$(cat "$goal"); else proposition="type_of% $goal"; fi
logs=$(mktemp -d "${TMPDIR:-/tmp}/try-tactics.XXXXXXXX") || exit 2
scratch=$(mktemp -d "${TMPDIR:-/tmp}/try-tactics-src.XXXXXXXX") || exit 2
trap 'rm -rf "$scratch"' EXIT
passed=0; i=0
for candidate in rfl decide omega "simp only" sol_prove sol_chain "$@"; do
  i=$((i+1)); file="$scratch/candidate$i.lean"; log="$logs/$i.log"
  printf "import %s\n\nexample : %s := by\n  %s\n" "$module" "$proposition" "$candidate" > "$file"
  start=$(date +%s)
  if lake env lean --tstack=131072 "$file" > "$log" 2>&1; then status=PASS; passed=1; else status=FAIL; fi
  end=$(date +%s); printf "%s %s %ss %s\n" "$status" "$candidate" "$((end-start))" "$log"
done
[ "$passed" -eq 1 ]
