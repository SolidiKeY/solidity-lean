#!/usr/bin/env bash
# Run the bytecode-selection witness checks locally, exactly as CI does: this script runs
# the command lines of the "Build the witnesses' imports" and "Check the witnesses" steps
# of .github/workflows/bytecode-selection-witnesses.yml (the single list of commands; see
# that file for what is checked and under which bounds), with a fresh temporary directory
# outside the checkout in place of the runner's RUNNER_TEMP.
# Uses the Lean of the repository's toolchain (elan resolves lean-toolchain). The imports
# are built by Lake, so seed its cache first (scripts/ci/fetch-lake-cache.sh) or expect a
# long cold build. Take the writer lock before running (docs/contributing.md).
# Usage: scripts/ci/bytecode-selection-witnesses.sh
# Exit 0: every witness compiled; 1: a command failed; 2: setup error.
set -uo pipefail
root=$(git rev-parse --show-toplevel) || exit 2
cd "$root" || exit 2
export PATH="$HOME/.elan/bin:$PATH"
workflow=.github/workflows/bytecode-selection-witnesses.yml
commands=$(sed -n 's/^          \(lake build \|python3 scripts\/ci\/restore-lake-artifacts\.py$\|mkdir -p \|[A-Z_0-9=$a-z\/ ]*lake env timeout \)/\1/p' "$workflow")
count=$(grep -c ' lake env timeout 300 lean ' <<<"$commands")
[ "$count" = 7 ] || { echo "bytecode-selection-witnesses: expected 7 witness commands in $workflow, found $count" >&2; exit 2; }
RUNNER_TEMP=$(mktemp -d) || exit 2
export RUNNER_TEMP
trap 'rm -rf "$RUNNER_TEMP"' EXIT
while IFS= read -r command; do
  start=$SECONDS
  if bash -c "$command"; then
    echo "PASS $((SECONDS - start))s ${command##* lean }"
  else
    echo "FAIL $((SECONDS - start))s $command" >&2
    exit 1
  fi
done <<<"$commands"
echo "bytecode-selection-witnesses: PASS ($count witnesses)"
