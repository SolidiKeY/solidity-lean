#!/bin/sh
set -eu
export PATH=/opt/node:/opt/lean/bin:$PATH
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= LAKE_ARTIFACT_CACHE=false
[ "$(cat /sys/fs/cgroup/memory.max)" = 12884901888 ]
[ "$(cat /sys/fs/cgroup/memory.swap.max)" = 0 ]
[ "$LAKE_CACHE_DIR" = "" ]
[ "$LAKE_ARTIFACT_CACHE" = false ]
[ "$LEAN_NUM_THREADS" = 1 ]
trap 'printf "H1_CGROUP_PEAK="; cat /sys/fs/cgroup/memory.peak' EXIT
lean --version
lake --version
while IFS= read -r module; do
  printf '\nH1_TARGET=%s\n' "$module"
  lake -f /workspace/v08-world-lowering-evidence/published-099-investigation-20261101/runtime-public099.toml build "$module"
done < /workspace/v08-world-lowering-evidence/h1-recovery-20261102/focused-modules.txt
