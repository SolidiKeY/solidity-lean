#!/usr/bin/env bash
set -uo pipefail
cd /workspace/v07-lowering || exit 2
label=cp17-coord-$(date +%s%N)-$$
if [ "${1:-}" = env ] && [ "${2:-}" = lean ]; then
 shift 2
 files=()
 for arg in "$@"; do
  case "$arg" in --tstack=131072|-j1) ;; --*) echo "unsupported option or stack budget: $arg" >&2; exit 78;; -*) echo "unsupported option or thread budget: $arg" >&2; exit 78;; /workspace/v07-evidence/*) files+=("/evidence/${arg#/workspace/v07-evidence/}");; *) files+=("$arg");; esac
 done
 sh tests/v07/run-bounded.sh "$label" --files "${files[@]}"; result=$?
elif [ "${1:-}" = build ] && [ "$#" -gt 1 ]; then
 shift
 sh tests/v07/run-bounded.sh "$label" "$@"; result=$?
else
 echo 'V07 bounded adapter: unsupported literal/default Lake invocation; no silent substitution' >&2
 exit 78
fi
cat "/workspace/v07-evidence/restart-20261102/$label.log"
exit "$result"
