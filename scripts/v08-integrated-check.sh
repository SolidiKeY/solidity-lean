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
  case "$module" in
    @shared-file)
      file=$(cat /workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt)
      case "$file" in
        /workspace/v08-world-lowering-published/Solidity/Lowering/V08/WorldImageAccess.lean|/workspace/v08-world-lowering-published/Solidity/Lowering/V08/WorldImageAccessControls.lean|/workspace/v08-world-lowering-published/Solidity/Lowering/V08/SourceClockTransactions.lean|/workspace/v08-world-lowering-published/Solidity/Lowering/V08/LocalCallableTransport.lean) ;;
        *) echo 'Unapproved per-file target' >&2; exit 2 ;;
      esac
      /opt/lean/bin/lake -f /workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/runtime-integrated.toml env lean --tstack=131072 -j1 "$file"
      continue ;;
  esac
  lake -f /workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/runtime-integrated.toml build "$module"
done < /workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/focused-modules.txt
