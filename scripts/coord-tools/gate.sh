#!/usr/bin/env bash
set -uo pipefail
usage() { echo "usage: gate.sh per-file FILE... | touched | checkpoint | full" >&2; exit 2; }
[ $# -gt 0 ] || usage
mode=$1; shift
case "$mode" in per-file) [ $# -gt 0 ] || usage;; touched|checkpoint|full) [ $# -eq 0 ] || usage;; *) usage;; esac
root=$(git rev-parse --show-toplevel) || exit 2
logs=${GATE_LOGS:-$(mktemp -d "${TMPDIR:-/tmp}/coord-gates.XXXXXXXX")}; mkdir -p "$logs" || exit 2
logs=$(cd "$logs" && pwd); : > "$logs/gates.tsv"
git rev-parse HEAD > "$logs/HEAD" || exit 2
if [ "$mode" = per-file ]; then
  # FILE paths are relative to the caller's directory; gates run from the root.
  files=(); here=$(pwd -P)
  for file in "$@"; do
    if [ "$here" = "$(cd "$root" && pwd -P)" ]; then files+=("$file"); else files+=("$(realpath -m -s --relative-to="$root" -- "$file")"); fi
  done
fi
cd "$root" || exit 2
failed=0; index=0
run_gate() {
  local name=$1; shift
  index=$((index+1)); local log="$logs/$index.log" start end seconds status cmd
  printf -v cmd "%q " "$@"; start=$(date +%s)
  if "$@" >"$log" 2>&1; then status=PASS; else status=FAIL; failed=1; fi
  end=$(date +%s); seconds=$((end-start))
  printf "%s %s %ss %s\n" "$status" "$name" "$seconds" "$log"
  printf "%s\t%s\t%s\t%s\t%s\n" "$status" "$name" "$seconds" "$log" "$cmd" >> "$logs/gates.tsv"
}
build_touched() {
  local base=${GATE_BASE:-origin/master}; local targets
  targets=$(python3 - "$base" <<'PY'
import pathlib,subprocess,sys
base=sys.argv[1]
def git(*args): return subprocess.check_output(["git",*args],text=True).splitlines()
merge=git("merge-base",base,"HEAD")[0]
files=set(git("diff","--name-only","--no-renames",merge,"--")) | set(git("ls-files","--others","--exclude-standard"))
mods={}
for p in pathlib.Path("Solidity").rglob("*.lean"):
    if str(p).startswith("Solidity/Scratch/"): continue
    mods[str(p)[:-5].replace("/",".")]=[line.split()[1] for line in p.read_text(errors="replace").splitlines() if line.startswith("import ") and len(line.split())>1]
rev={}
for m,imports in mods.items():
    for dep in imports: rev.setdefault(dep,set()).add(m)
out={p[:-5].replace("/",".") for p in files if p.endswith(".lean") and (p.startswith("Solidity/") or p=="Solidity.lean")}
stack=list(out)
while stack:
    for m in rev.get(stack.pop(),()):
        if m not in out: out.add(m); stack.append(m)
print(" ".join(sorted(out & mods.keys())))
PY
) || return 1
  echo "targets: ${targets:-none}"
  [ -z "$targets" ] || LEAN_NUM_THREADS=1 lake build $targets
}
if [ "$mode" = per-file ]; then
  for file in "${files[@]}"; do run_gate "lean:$file" lake env lean --tstack=131072 "$file"; done
else
  run_gate build-touched build_touched
  if [ "$mode" != touched ]; then
    run_gate run-lean bash run-lean.sh
    run_gate trust bash scripts/check-trust.sh
    run_gate orphans node scripts/check-orphans.mjs
    run_gate layers node scripts/check-layers.mjs
    run_gate doc-paths bash scripts/check-doc-paths.sh
    run_gate axiom-pins node scripts/check-axiom-pins.mjs
  fi
  if [ "$mode" = full ]; then
    run_gate testsuite bash scripts/check-testsuite.sh
    run_gate corpus bash scripts/check-corpus.sh
    run_gate automatic-strict node scripts/check-automatic.mjs --strict
  fi
fi
exit "$failed"
