#!/usr/bin/env bash
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= LEAN_LSP_MAX_OPEN_FILES=1
export PATH="$PWD/.lake/native-browser-rowsnine-gates/bin:$PATH"
export LEAN_MCP_SOCKDIR="$PWD/.lake/nb-rb6513-mcp"
mkdir -p "$LEAN_MCP_SOCKDIR"
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
trap 'python3 scripts/coord-tools/lean-mcp stop' EXIT
lean --version
/workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version
cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max /sys/fs/cgroup/cpu.max
export GATE_LOGS=/workspace/scratch/browser-chain/readbounds-6513/post-rebase-controls
bash scripts/coord-tools/gate.sh per-file tests/directruntime-20261104/shared-translator/ReadBoundsStackControls.lean
