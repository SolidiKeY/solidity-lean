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
for module in Solidity.Calculus.ReadBoundsStack Solidity.Calculus.ReadBounds Solidity.Calculus.ReadBoundsStackCorrect Solidity.Tools.DirectRuntime; do
  timeout --kill-after=10s 300s lake build "$module"
done
for file in Solidity/Calculus/ReadBoundsStack.lean Solidity/Calculus/ReadBounds.lean Solidity/Calculus/ReadBoundsStackCorrect.lean tests/directruntime-20261104/shared-translator/ReadBoundsStackControls.lean; do
 timeout --kill-after=10s 300s python3 scripts/coord-tools/lean-mcp diag "$file"
done
lake build solkeycheck
.lake/build/bin/solkeycheck --key "$SOLKEY_RULES"
