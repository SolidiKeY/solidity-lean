#!/usr/bin/env bash
# Full SOL-EU kernel gate: writes the header `check-sol-expression-uniqueness.py
# --checkpoint --build-log LOG` requires (current source digest), then runs the
# repository's full `./run-lean.sh` and records its exit status.
# Usage: tests/sol-expression-uniqueness/gate.sh LOG
set -u
[ $# -eq 1 ] || { echo "usage: $0 LOG" >&2; exit 2; }
log=$(realpath -m "$1")
cd "$(dirname "$0")/../.." || exit 2
{
  echo "SOL_EU_HEAD $(git rev-parse HEAD)"
  echo "SOL_EU_SOURCES $(python3 scripts/check-sol-expression-uniqueness.py --source-digest)"
  echo "SOL_EU_FULL_GATE ./run-lean.sh"
  start=$(date +%s)
  ./run-lean.sh
  status=$?
  echo "SOL_EU_SECONDS $(( $(date +%s) - start ))"
  echo "SOL_EU_EXIT $status"
} > "$log" 2>&1
grep '^SOL_EU_EXIT' "$log"

exit "$status"
