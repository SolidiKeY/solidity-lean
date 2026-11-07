#!/usr/bin/env bash
set -eu
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LEAN_LSP_MAX_OPEN_FILES=1
export PATH="/workspace/solidity-lean/tests/calldata-packets-1105/RawBool/bin:$PATH"
test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888
test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0
exec timeout 180 bash scripts/run-lean-mcp.sh
