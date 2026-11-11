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
  if "$@" >"$log" 2>&1; then
    status=PASS
  else
    status=FAIL
    # Retry only failed build steps with the observed shared-cache SIGBUS marker.
    case "$name" in
      build-touched|library|examples|run-lean|lean:*)
        if grep -Fq -- 'Lean exited with code 135' "$log"; then
          if ! cp -- "$log" "$log.first"; then
            failed=1
            printf "FAIL %s log-preservation %s\n" "$name" "$log" >&2
            return 1
          fi
          echo "RETRY-SIGBUS $name" | tee -a "$log"
          if "$@" >>"$log" 2>&1; then status=PASS; fi
        fi;;
    esac
    [ "$status" = PASS ] || failed=1
  fi
  end=$(date +%s); seconds=$((end-start))
  printf "%s %s %ss %s\n" "$status" "$name" "$seconds" "$log"
  printf "%s\t%s\t%s\t%s\t%s\n" "$status" "$name" "$seconds" "$log" "$cmd" >> "$logs/gates.tsv"
}
build_touched() {
  local base=${GATE_BASE:-origin/master}; local targets
  rm -f "$logs/core"
  targets=$(GATE_CORE_FILE="$logs/core" GATE_MODE="$mode" python3 - "$base" <<'PY'
import os,pathlib,subprocess,sys
base=sys.argv[1]
def git(*args): return subprocess.check_output(["git",*args],text=True).splitlines()
merge=git("merge-base",base,"HEAD")[0]
files=set(git("diff","--name-only","--no-renames",merge,"--")) | set(git("ls-files","--others","--exclude-standard"))
def eligible(p):
    return p == "Solidity.lean" or (p.startswith("Solidity/") and p.endswith(".lean") and not p.startswith("Solidity/Scratch/"))
mods={}
for p in pathlib.Path("Solidity").rglob("*.lean"):
    if not eligible(str(p)): continue
    mods[str(p)[:-5].replace("/",".")]=[line.split()[1] for line in p.read_text(errors="replace").splitlines() if line.startswith("import ") and len(line.split())>1]
rev={}
for m,imports in mods.items():
    for dep in imports: rev.setdefault(dep,set()).add(m)
touched={p[:-5].replace("/",".") for p in files if eligible(p)}
out=set(touched); stack=list(out)
while stack:
    for m in rev.get(stack.pop(),()):
        if m not in out: out.add(m); stack.append(m)
# The examples, the TestSuite and the corpus are their own libraries: a lane
# builds the dependents it touched among them only when it touches the core
# (Syntax, Semantics, Calculus) or sets GATE_EXAMPLES=1 (docs/contributing.md).
core=any("." in m and m.split(".")[1] in ("Syntax","Semantics","Calculus") for m in touched) or "SolidityExamples.lean" in files
wide=core or os.environ.get("GATE_EXAMPLES")=="1"
leaf=lambda m: "." in m and m.split(".")[1] in ("Examples","TestSuite","Corpus")
# what a touched example, TestSuite or corpus module reaches among those leaves
leafs={m for m in touched if leaf(m)}; stack=list(leafs)
while stack:
    for m in rev.get(stack.pop(),()):
        if leaf(m) and m not in leafs: leafs.add(m); stack.append(m)
out={m for m in out if wide or m in leafs or not leaf(m)}
# H109: checkpoint never builds the slow library, including transitive importers.
if os.environ.get("GATE_MODE") == "checkpoint":
    slow={line.split()[1] for line in pathlib.Path("SoliditySlowExamples.lean").read_text().splitlines() if line.startswith("import ")}
    out.difference_update(slow)
    # t2-controls-off-path: nor the SolidityControls library (built by full).
    ctl=pathlib.Path("SolidityControls.lean")
    if ctl.is_file():
        out.difference_update(l.split()[1] for l in ctl.read_text().splitlines() if l.startswith("import "))
print(" ".join(sorted(m for m in out if pathlib.Path(m.replace(".","/")+".lean").is_file())))
open(os.environ["GATE_CORE_FILE"],"w").write("core" if core else "")
PY
) || return 1
  echo "targets: ${targets:-none}"
  [ -z "$targets" ] || LEAN_NUM_THREADS=1 lake build $targets
}
if [ "$mode" = per-file ]; then
  for file in "${files[@]}"; do run_gate "lean:$file" lake lean "$file" -- --tstack=131072; done
else
  # Merge pre-gates use touched mode: reject the prospective tree before builds.
  run_gate layers node scripts/check-layers.mjs
  run_gate private-paths bash scripts/check-private-paths.sh
  run_gate evidence-files bash scripts/check-evidence-files.sh
  # CI's `checks` job runs this same script (.github/workflows/lean.yml), so a
  # tree that passes the gate cannot turn `checks` red.
  run_gate checks-fast bash scripts/ci/checks-fast.sh
  # t2-controls-off-path: every *Controls module in exactly one root, moved ones unreachable.
  run_gate controls-roots python3 scripts/coord-tools/controls-classify.py --check
  [ "$failed" -eq 0 ] || exit "$failed"
  run_gate build-touched build_touched
  if [ "$mode" != touched ]; then
    if [ "$mode" = full ]; then
      # H134: each slow example under its own 600 s one-core budget, as in CI
      # (after the libraries it imports); run-lean.sh then finds them built.
      run_gate library lake build Solidity SolidityExamples SolidityControls
      run_gate slow-examples bash scripts/ci/build-slow-examples.sh
      run_gate run-lean bash run-lean.sh
    else
      # A checkpoint builds the library alone; a lane touching the core also
      # builds the examples and the TestSuite (`docs/contributing.md`).
      run_gate library lake build Solidity
      if [ -s "$logs/core" ] || [ "${GATE_EXAMPLES:-0}" = 1 ]; then
        run_gate examples lake build SolidityExamples SolkeyTestSuite
      fi
    fi
    # trust, roots, fragments, doc-paths and axiom-pins ran in checks-fast.
    run_gate orphans node scripts/check-orphans.mjs
    run_gate p16-generated python3 -B scripts/h62/item1/p16-generator/check.py
  fi
  if [ "$mode" = full ]; then
    run_gate testsuite bash scripts/check-testsuite.sh
    run_gate corpus bash scripts/check-corpus.sh
    run_gate automatic-strict node scripts/check-automatic.mjs --strict
  fi
fi
exit "$failed"
