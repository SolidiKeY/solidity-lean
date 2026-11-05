#!/bin/sh
trap 'exit 0' TERM INT
while :; do
 rss=0
 missing=0
 for p in /proc/[0-9]*/status; do
  if n=$(awk '/^VmRSS:/ {print $2}' "$p" 2>/dev/null); then
   rss=$((rss+${n:-0}))
  else
   missing=$((missing+1))
  fi
 done
 printf '%s %s %s %s %s\n' "$(date +%s)" "$rss" "$missing" "$(cat /sys/fs/cgroup/memory.current)" "$(cat /sys/fs/cgroup/memory.peak)"
 sleep 1 &
 wait $! || :
done
