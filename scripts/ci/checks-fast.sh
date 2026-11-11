#!/usr/bin/env bash
# The fast checks: every check of lean.yml's `checks` job, none of which needs a Lean build.
# CI's `checks` job and `scripts/coord-tools/gate.sh` (touched, checkpoint, full) both run
# this one script, so a tree that passes the lane gate cannot turn `checks` red.
# Needs node >= 22, python3 and the full Git history (the H107/H112 shrink-only baselines
# compare every merge parent). Writes nothing in the tree.
#
# Usage: scripts/ci/checks-fast.sh [--list] [--serial] [NAME...]
#   NAME...   run only the named checks (see --list)
#   --serial  one check at a time (default: up to CHECKS_FAST_JOBS, default nproc, at once)
# Prints "PASS|FAIL <name> <seconds>s" per check and the tail of each failing log.
# Exit 0: every check passed; 1: a check failed; 2: usage error.
set -uo pipefail
root=$(git rev-parse --show-toplevel) || exit 2
cd "$root" || exit 2

# name<TAB>command, in lean.yml's former step order.
checks=$(cat <<'EOF'
trust-test	node --test scripts/check-trust.test.mjs
trust	bash scripts/check-trust.sh
private-paths	bash scripts/check-private-paths.sh
evidence-files	bash scripts/check-evidence-files.sh
site-exporter	node --test scripts/site/export.test.mjs
dafny-features	node scripts/check-dafny-features.mjs
axiom-pin-tests	node --test scripts/check-axiom-pins.test.mjs tests/h62/item5/statement-graph/h112-tooling.test.mjs
w0-tooling	python3 -B tests/h62/item5/statement-graph/test_w0_tooling.py -v
doc-paths	bash scripts/check-doc-paths.sh
doc-navigation	python3 scripts/check-doc-navigation.py
axiom-pins	node scripts/check-axiom-pins.mjs
layers	node scripts/check-layers.mjs
roots	bash scripts/coord-tools/register.sh --check
fragments	bash scripts/coord-tools/fragments.sh --check
slow-partition	python3 -B tests/h55/module-times/test_slow_examples.py
solidity-features	python3 scripts/solidity-feature-audit.py --check
lean-budget-test	python3 -B scripts/lean-budget/test_check.py
lean-budget	python3 -B scripts/lean-budget/check.py
EOF
)

jobs=${CHECKS_FAST_JOBS:-$(nproc 2>/dev/null || echo 2)}
selected=()
for arg in "$@"; do
  case "$arg" in
    --list) cut -f1 <<<"$checks"; exit 0;;
    --serial) jobs=1;;
    -*) echo "checks-fast: unknown option $arg" >&2; exit 2;;
    *) grep -q "^$arg	" <<<"$checks" || { echo "checks-fast: unknown check $arg" >&2; exit 2; }
       selected+=("$arg");;
  esac
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

logs=$(mktemp -d "${TMPDIR:-/tmp}/checks-fast.XXXXXXXX") || exit 2
names=()
while IFS=$'\t' read -r name cmd; do
  if [ ${#selected[@]} -gt 0 ] && ! printf '%s\n' "${selected[@]}" | grep -qx -- "$name"; then continue; fi
  names+=("$name")
  while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do wait -n 2>/dev/null || true; done
  (
    start=$(date +%s)
    bash -c "$cmd" >"$logs/$name.log" 2>&1 </dev/null; status=$?
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
