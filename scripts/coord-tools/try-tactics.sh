#!/usr/bin/env bash
set -uo pipefail
[ $# -ge 2 ] || { echo "usage: try-tactics.sh MODULE GOAL [CANDIDATE...]" >&2; exit 2; }
module=$1; goal=$2; shift 2
if [ -f "$goal" ]; then proposition=$(cat "$goal"); else proposition="type_of% $goal"; fi
logs=$(mktemp -d "${TMPDIR:-/tmp}/try-tactics.XXXXXXXX") || exit 2
scratch=$(mktemp -d "${TMPDIR:-/tmp}/try-tactics-src.XXXXXXXX") || exit 2
mcpfile=
trap '[ -z "$mcpfile" ] || rm -f "$mcpfile"; rm -rf "$scratch"' EXIT
backend=${TRY_TACTICS_BACKEND:-auto}
bridge=$(dirname "$0")/lean-mcp
case "$backend" in
  auto) if [ -f "$bridge" ] && python3 "$bridge" status >/dev/null 2>&1; then backend=mcp; else backend=lake; fi;;
  lake|mcp) ;;
  *) echo "invalid TRY_TACTICS_BACKEND" >&2; exit 2;;
esac
passed=0; i=0; bridge_error=0
for candidate in rfl decide omega "simp only" sol_prove sol_chain "$@"; do
  i=$((i+1)); file="$scratch/candidate$i.lean"; log="$logs/$i.log"
  printf "import %s\n\nexample : %s := by\n  %s\n" "$module" "$proposition" "$candidate" > "$file"
  start=$(date +%s)
  if [ "$backend" = mcp ]; then
    root=$(git rev-parse --show-toplevel) || exit 2
    mcpfile=$(mktemp "$root/TerraTryXXXXXX.lean") || exit 2
    printf "import %s\n\nexample : %s := by\n  sorry\n" "$module" "$proposition" > "$mcpfile"
    line=$(( $(printf "%s\n" "$proposition" | wc -l) + 3 ))
    python3 "$bridge" try "$mcpfile" "$line" "$candidate" > "$log" 2>&1; rc=$?
    if [ $rc -eq 0 ]; then status=PASS; passed=1; elif [ $rc -eq 1 ]; then status=FAIL; else status=FAIL; bridge_error=1; fi
    rm -f "$mcpfile"; mcpfile=
  elif lake env lean --tstack=131072 "$file" > "$log" 2>&1 && ! grep -q "declaration uses 'sorry'" "$log"; then status=PASS; passed=1; else status=FAIL; fi
  end=$(date +%s); printf "%s %s %ss %s\n" "$status" "$candidate" "$((end-start))" "$log"
done
[ "$passed" -eq 1 ] && exit 0
[ "$bridge_error" -eq 0 ] || { echo "try-tactics: lean-mcp bridge error; see the FAIL logs" >&2; exit 2; }
exit 1
