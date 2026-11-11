#!/usr/bin/env bash
# The fast checks: every check CI's lean.yml `checks` job, trust.yml and prose-budget.yml run
# without a full library build. `scripts/coord-tools/gate.sh` (touched, checkpoint, full) runs
# them all; CI's lean.yml `checks` job runs its own (`--workflow lean.yml`), so a tree that
# passes the lane gate cannot turn those checks red. scripts/ci/ci-only.tsv lists every CI step
# not covered here, with its reason (checked by the `ci-coverage` check).
# Needs node >= 22, python3, the full Git history (the H107/H112 shrink-only baselines compare
# every merge parent), and for the `lean` checks elan on PATH and the fetched Lake cache
# (scripts/ci/fetch-lake-cache.sh): they `lake build` their own imports. Writes nothing in the
# tree but Lake's build outputs.
#
# Usage: scripts/ci/checks-fast.sh [--list] [--serial] [--workflow FILE] [NAME...]
#   NAME...          run only the named checks (see --list; names are stable)
#   --workflow FILE  run only the checks CI runs in FILE (lean.yml, trust.yml, prose-budget.yml)
#   --serial         one check at a time (default: up to CHECKS_FAST_JOBS, default nproc, at
#                    once; `lean` checks always take turns, holding one lock)
# Prints "PASS|FAIL <name> <seconds>s" per check and the tail of each failing log.
# Exit 0: every check passed; 1: a check failed; 2: usage error.
set -uo pipefail
root=$(git rev-parse --show-toplevel) || exit 2
cd "$root" || exit 2

# name<TAB>CI workflow that runs it<TAB>lean (needs Lake; takes the lock) or -<TAB>command.
# Names are stable: the factory compares them with master's.
checks=$(cat <<'EOF'
trust-test	lean.yml	-	node --test scripts/check-trust.test.mjs
trust	lean.yml	-	bash scripts/check-trust.sh
private-paths	lean.yml	-	bash scripts/check-private-paths.sh
evidence-files	lean.yml	-	bash scripts/check-evidence-files.sh
site-exporter	lean.yml	-	node --test scripts/site/export.test.mjs
dafny-features	lean.yml	-	node scripts/check-dafny-features.mjs
axiom-pin-tests	lean.yml	-	node --test scripts/check-axiom-pins.test.mjs tests/h62/item5/statement-graph/h112-tooling.test.mjs
w0-tooling	lean.yml	-	python3 -B tests/h62/item5/statement-graph/test_w0_tooling.py -v
doc-paths	lean.yml	-	bash scripts/check-doc-paths.sh
doc-navigation	lean.yml	-	python3 scripts/check-doc-navigation.py
axiom-pins	lean.yml	-	node scripts/check-axiom-pins.mjs
layers	lean.yml	-	node scripts/check-layers.mjs
roots	lean.yml	-	bash scripts/coord-tools/register.sh --check
fragments	lean.yml	-	bash scripts/coord-tools/fragments.sh --check
slow-partition	lean.yml	-	python3 -B tests/h55/module-times/test_slow_examples.py
solidity-features	lean.yml	-	python3 scripts/solidity-feature-audit.py --check
ci-coverage	lean.yml	-	python3 -B scripts/ci/check-ci-coverage.py
prose-budget	prose-budget.yml	-	python3 -m unittest discover -s scripts/check-prose-budget-tests && python3 scripts/check-prose-budget
trust-tests	trust.yml	lean	node --test scripts/trust/trust-*.test.mjs
trust-closure	trust.yml	lean	node scripts/trust/trust-closure.mjs --source-ceilings
trust-implemented-by	trust.yml	lean	node scripts/trust/trust-implemented-by.mjs
EOF
)

jobs=${CHECKS_FAST_JOBS:-$(nproc 2>/dev/null || echo 2)}
selected=() workflow=""
while [ $# -gt 0 ]; do
  case "$1" in
    --list) cut -f1,2 <<<"$checks"; exit 0;;
    --serial) jobs=1;;
    --workflow) workflow=${2:-}; shift
      cut -f2 <<<"$checks" | grep -qx -- "$workflow" || { echo "checks-fast: no checks for workflow '$workflow'" >&2; exit 2; };;
    -*) echo "checks-fast: unknown option $1" >&2; exit 2;;
    *) grep -q "^$1	" <<<"$checks" || { echo "checks-fast: unknown check $1" >&2; exit 2; }
       selected+=("$1");;
  esac
  shift
done
case "$jobs" in ''|*[!0-9]*|0) echo "checks-fast: CHECKS_FAST_JOBS must be a positive integer" >&2; exit 2;; esac

# The environment CI gives these checks; a gate run without it could pass where CI fails.
if [ "$(git rev-parse --is-shallow-repository)" != false ]; then
  echo "checks-fast: shallow clone; the shrink-only baselines need full history (git fetch --unshallow)" >&2; exit 1
fi
node_major=$(node -p 'process.versions.node.split(".")[0]' 2>/dev/null) || node_major=0
if [ "${node_major:-0}" -lt 22 ]; then echo "checks-fast: node >= 22 required (have ${node_major:-none})" >&2; exit 1; fi

untracked=$(git ls-files --others --exclude-standard | wc -l)
[ "$untracked" -eq 0 ] || echo "checks-fast: warning: $untracked untracked file(s) are checked here but absent from CI's checkout; commit or remove them"

export PATH="$HOME/.elan/bin:$PATH"
# No __pycache__ in the tree from a check that imports test modules.
export PYTHONDONTWRITEBYTECODE=1
logs=$(mktemp -d "${TMPDIR:-/tmp}/checks-fast.XXXXXXXX") || exit 2
# The `lean` checks run `lake build`/`lake lean` in this workspace: one at a time.
lock="$logs/lake.lock"; : > "$lock"
names=()
while IFS=$'\t' read -r name wf kind cmd; do
  if [ ${#selected[@]} -gt 0 ] && ! printf '%s\n' "${selected[@]}" | grep -qx -- "$name"; then continue; fi
  if [ -n "$workflow" ] && [ "$wf" != "$workflow" ]; then continue; fi
  names+=("$name")
  while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do wait -n 2>/dev/null || true; done
  (
    start=$(date +%s)
    if [ "$kind" = lean ]; then flock "$lock" bash -c "$cmd" >"$logs/$name.log" 2>&1 </dev/null; status=$?
    else bash -c "$cmd" >"$logs/$name.log" 2>&1 </dev/null; status=$?; fi
    echo "$status $(( $(date +%s) - start ))" > "$logs/$name.status"
  ) &
done <<<"$checks"
wait

failed=0
for name in "${names[@]}"; do
  read -r status seconds < "$logs/$name.status" || { status=1; seconds=?; }
  if [ "$status" -eq 0 ]; then echo "PASS $name ${seconds}s"; else
    failed=1; echo "FAIL $name ${seconds}s (exit $status)"
  fi
done
for name in "${names[@]}"; do
  read -r status _ < "$logs/$name.status" 2>/dev/null || status=1
  [ "$status" -eq 0 ] && continue
  echo "--- $name: last 40 lines"; tail -n 40 "$logs/$name.log"
done
[ -n "${CHECKS_FAST_KEEP_LOGS:-}" ] && echo "checks-fast: logs in $logs" || rm -rf "$logs"
exit "$failed"
