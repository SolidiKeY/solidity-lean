#!/usr/bin/env bash
# Heartbeat collector: one JSON line per module (scripts/heartbeats/README.md).
set -uo pipefail
usage() {
  echo "usage: collect.sh [--timeout S] [--write BASELINE | --check BASELINE [--tolerance PCT] [--min UNITS]] MODULE|FILE.lean..." >&2
  exit 2
}
root=$(cd "$(dirname "$0")/../.." && pwd) || exit 2
here=$(pwd)
timeout_s="" mode="" baseline="" ratchet_args=()
while [ $# -gt 0 ]; do
  case "$1" in
    --timeout) [ $# -ge 2 ] || usage; timeout_s=$2; shift 2;;
    --write|--check) [ $# -ge 2 ] && [ -z "$mode" ] || usage; mode=${1#--}; baseline=$2; shift 2;;
    --tolerance|--min) [ $# -ge 2 ] || usage; ratchet_args+=("$1" "$2"); shift 2;;
    --) shift; break;;
    -*) usage;;
    *) break;;
  esac
done
[ $# -gt 0 ] || usage
[ ${#ratchet_args[@]} -eq 0 ] || [ "$mode" = check ] || usage
case "$baseline" in ""|/*) ;; *) baseline=$here/$baseline;; esac
cd "$root" || exit 2
# The driver is a lake exe outside the default targets; a no-op when current.
lake build hbcollect >&2 || { echo "collect.sh: cannot build hbcollect" >&2; exit 2; }
exe=$root/.lake/build/bin/hbcollect
out=$(mktemp "${TMPDIR:-/tmp}/heartbeats.XXXXXX") || exit 2
trap 'rm -f "$out"' EXIT
status=0
for arg in "$@"; do
  case "$arg" in
    *.lean) # a file outside the checkout is named by its basename
      file=$(realpath -m --relative-to="$root" -- "$(cd "$here" && realpath -m -- "$arg")")
      case "$file" in ../*) file=$(cd "$here" && realpath -m -- "$arg"); mod=$(basename "$file" .lean);;
        *) mod=${file%.lean}; mod=${mod//\//.};; esac;;
    *) mod=$arg; file=${arg//.//}.lean;;
  esac
  [ -f "$file" ] || { echo "collect.sh: no file $file for $mod" >&2; status=2; continue; }
  cmd=("$exe" "$file" "$mod")
  [ -z "$timeout_s" ] || cmd=(timeout "$timeout_s" "${cmd[@]}")
  # Elab.async=false is set by the driver; one thread and a 128 MiB stack
  # (the library's --tstack=131072) keep the counts deterministic.
  ( ulimit -s 131072 && LEAN_NUM_THREADS=1 lake env "${cmd[@]}" ) | tee -a "$out"
  rc=${PIPESTATUS[0]}
  if [ "$rc" -ne 0 ]; then
    echo "collect.sh: $mod exited with $rc" >&2
    [ "$rc" -eq 124 ] && status=124 || [ "$status" -ne 0 ] || status=1
  fi
done
if [ -n "$mode" ]; then
  python3 "$root/scripts/heartbeats/collect.d/ratchet.py" "$mode" "$baseline" "$out" "${ratchet_args[@]}" || { [ "$status" -ne 0 ] || status=1; }
fi
exit "$status"
