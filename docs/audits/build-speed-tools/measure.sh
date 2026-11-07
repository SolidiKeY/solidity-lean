#!/usr/bin/env bash
# Time and peak RSS of one cold elaboration per file, one at a time, through
# the repository's own per-file gate (`gate.sh per-file`, i.e. `lake env lean
# --tstack=131072 FILE`). Prints TSV: module wall_s cpu_s peak_rss_mb status.
# Peak RSS is the largest VmHWM seen while sampling the `lean` process every
# 0.2 s (VmHWM is the kernel's own high-water mark, so only growth in the last
# 0.2 s can be missed). Usage: measure.sh FILE... >> times.tsv
set -uo pipefail
root=$(git rev-parse --show-toplevel); cd "$root"
export PATH="$HOME/.elan/bin:$PATH"
for f in "$@"; do
  mod=${f%.lean}; mod=${mod//\//.}
  hwm_file=$(mktemp)
  echo 0 > "$hwm_file"
  ( peak=0
    while :; do
      for p in $(pgrep -x lean); do
        if tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null | grep -qF -- "$f"; then
          h=$(awk '/VmHWM/{print $2}' /proc/$p/status 2>/dev/null)
          [ -n "$h" ] && [ "$h" -gt "$peak" ] && { peak=$h; echo "$peak" > "$hwm_file"; }
        fi
      done
      sleep 0.2
    done ) & sampler=$!
  TIMEFORMAT='%R %U %S'
  t=$( { time GATE_LOGS=$(mktemp -d) scripts/coord-tools/gate.sh per-file "$f" >/dev/null 2>&1; echo "rc=$?" >&2; } 2>&1 )
  kill $sampler 2>/dev/null; wait $sampler 2>/dev/null
  rc=$(echo "$t" | sed -n 's/^rc=//p'); read -r wall user sys < <(echo "$t" | grep -v '^rc=' | tail -1)
  cpu=$(echo "$user + $sys" | bc)
  printf "%s\t%s\t%s\t%d\t%s\n" "$mod" "$wall" "$cpu" "$(( $(cat "$hwm_file") / 1024 ))" "$([ "$rc" = 0 ] && echo ok || echo FAIL)"
  rm -f "$hwm_file"
done
