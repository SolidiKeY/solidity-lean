#!/usr/bin/env bash
# Heartbeat collector: one JSON line per module (scripts/heartbeats/README.md).
set -uo pipefail
usage() {
  echo "usage: collect.sh [--lake] [--timeout S] [--write BASELINE | --check BASELINE [--tolerance PCT] [--min UNITS]] MODULE|PATH.lean..." >&2
  exit 2
}
root=$(cd "$(dirname "$0")/../.." && pwd) || exit 2
here=$(pwd)
timeout_s="" mode="" baseline="" ratchet_args=() lake=0
while [ $# -gt 0 ]; do
  case "$1" in
    --lake) lake=1; shift;;
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
fake=""
trap 'rm -rf "$out" "$fake"' EXIT
if [ "$lake" = 1 ]; then
  # --lake: Lake builds the module and runs the driver where it would run `lean`, so the
  # one elaboration that is counted also leaves the .olean/.ilean/.c, hashes and trace
  # that Lake (and its artifact cache) accept as current. Lake takes its `lean` from
  # LEAN_SYSROOT: a copy of the toolchain made of links, whose bin/lean hands the one
  # module in HBCOLLECT_FILE to the driver and everything else to the real `lean`.
  # A module's trace names the toolchain by `lean --githash`, which is unchanged.
  sysroot=$(lean --print-prefix) && [ -x "$sysroot/bin/lean" ] || { echo "collect.sh: no lean toolchain" >&2; exit 2; }
  fake=$(mktemp -d "${TMPDIR:-/tmp}/heartbeats-sysroot.XXXXXX") || exit 2
  mkdir "$fake/bin" && ln -s "$sysroot"/* "$fake/" 2>/dev/null
  ln -s "$sysroot"/bin/* "$fake/bin/" && rm -f "$fake/bin/lean" || exit 2
  # Same run as below: one thread and a 128 MiB main-thread stack.
  cat >"$fake/bin/lean" <<EOF
#!/bin/sh
if [ -n "\${HBCOLLECT_FILE:-}" ]; then
  for a in "\$@"; do
    [ "\$a" != "\$HBCOLLECT_FILE" ] || { ulimit -s 131072 && LEAN_NUM_THREADS=1 exec '$exe' --lean "\$HBCOLLECT_REPORT" "\$@"; exit 2; }
  done
fi
exec '$sysroot/bin/lean' "\$@"
EOF
  chmod +x "$fake/bin/lean" || exit 2
fi
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
  if [ "$lake" = 1 ]; then
    one=$fake/report; : >"$one"
    # -q: warnings and errors only, not one line per fetched import.
    cmd=(lake -q build "$mod")
    [ -z "$timeout_s" ] || cmd=(timeout --kill-after=10s "$timeout_s" "${cmd[@]}")
    HBCOLLECT_FILE=$root/$file HBCOLLECT_REPORT=$one LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=$fake \
      "${cmd[@]}" >&2 </dev/null
    rc=$?; [ "$rc" -ne 137 ] || rc=124
    # Lake does not run `lean` for a module that is already up to date: no line then.
    [ -s "$one" ] || echo "collect.sh: $mod was not elaborated (up to date, or its build stopped before it)" >&2
    tee -a "$out" <"$one"
  else
    cmd=("$exe" "$file" "$mod")
    [ -z "$timeout_s" ] || cmd=(timeout "$timeout_s" "${cmd[@]}")
    # Elab.async=false is set by the driver; one thread and a 128 MiB stack
    # (the library's --tstack=131072) keep the counts deterministic.
    ( ulimit -s 131072 && LEAN_NUM_THREADS=1 lake env "${cmd[@]}" ) | tee -a "$out"
    rc=${PIPESTATUS[0]}
  fi
  if [ "$rc" -ne 0 ]; then
    echo "collect.sh: $mod exited with $rc" >&2
    [ "$rc" -eq 124 ] && status=124 || [ "$status" -ne 0 ] || status=1
  fi
done
if [ -n "$mode" ]; then
  python3 "$root/scripts/heartbeats/collect.d/ratchet.py" "$mode" "$baseline" "$out" "${ratchet_args[@]}" || { [ "$status" -ne 0 ] || status=1; }
fi
exit "$status"
