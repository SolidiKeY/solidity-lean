#!/usr/bin/env bash
# Profile one module without touching it: copy it to OUTDIR with
# `set_option profiler true` (threshold MS, default 300) after its imports,
# elaborate the copy through `gate.sh per-file`, and keep the gate log.
# Optional STRIP=regex deletes matching lines from the copy (e.g. axiom pins)
# to measure their share; STRIP_PINS=1 deletes every `#guard_msgs in #print
# axioms` pin with its expected-output docstring; SED=script edits the copy
# (e.g. a chunk size) and TAG names the variant. Usage: profile.sh FILE OUTDIR [MS]
set -uo pipefail
f=$1; out=$2; ms=${3:-300}
root=$(git rev-parse --show-toplevel); cd "$root"; export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$out"; base=$(basename "$f" .lean); sfx=${STRIP:+.stripped}${STRIP_PINS:+.nopins}${TAG:+.$TAG}
# The copy sits under Solidity/Scratch/ (in no library, git-ignored by
# convention, deleted below) at the original's depth, so relative paths such as
# `solc_import "../../../tests/…"` still resolve.
slashes=$(tr -cd / <<< "$f" | wc -c); dir=Solidity/Scratch
for ((i = 2; i < slashes; i++)); do dir=$dir/p; done
mkdir -p "$dir"; copy="$dir/${base}AuditProf${sfx//./_}.lean"
last=$(grep -n '^import ' "$f" | tail -1 | cut -d: -f1)
{ head -n "$last" "$f"; printf 'set_option profiler true\nset_option profiler.threshold %s\n' "$ms"
  tail -n +"$((last+1))" "$f" | { if [ -n "${STRIP:-}" ]; then grep -Ev -- "$STRIP"; else cat; fi; } \
  | { if [ -n "${STRIP_PINS:-}" ]; then python3 -c 'import re,sys; s=sys.stdin.read(); r=re.compile(r"/-- info: [^\n]*?(?:depends on axioms|does not depend).*?-/\s*#guard_msgs(?:\s*\([^)]*\))?\s*in\s*#print axioms[^\n]*\n", re.S); out,n=r.subn("",s); sys.stderr.write(f"stripped {n} pins\n"); sys.stdout.write(out)'; else cat; fi; } | sed -e "${SED:-}"; } > "$copy"
logs=$(mktemp -d); TIMEFORMAT='%R %U %S'
{ time GATE_LOGS=$logs scripts/coord-tools/gate.sh per-file "$copy" >/dev/null; } 2> "$out/$base$sfx.time"
cp "$logs/1.log" "$out/$base$sfx.prof"; cp "$copy" "$out/$base$sfx.lean"
rm -f "$copy"; rmdir -p "$dir" 2>/dev/null || true
echo "$(cat "$out/$base$sfx.time") $(grep -c 'error' "$out/$base$sfx.prof") errors -> $out/$base$sfx.prof"
