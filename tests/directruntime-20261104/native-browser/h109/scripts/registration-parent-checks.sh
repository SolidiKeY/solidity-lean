#!/usr/bin/env bash
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= LEAN_LSP_MAX_OPEN_FILES=1
export PATH="$PWD/.lake/native-browser-rowsnine-gates/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
export LEAN_MCP_SOCKDIR="$PWD/.lake/nb-rownine-mcp"
mkdir -p "$LEAN_MCP_SOCKDIR"
trap 'python3 scripts/coord-tools/lean-mcp stop' EXIT
/workspace/.setup/tools/lean-4.24.0-linux/bin/lean --version
/workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version
python3 - <<'PY'
from pathlib import Path
print('memory.max='+Path('/sys/fs/cgroup/memory.max').read_text().strip())
print('memory.swap.max='+Path('/sys/fs/cgroup/memory.swap.max').read_text().strip())
print('cpu.max='+Path('/sys/fs/cgroup/cpu.max').read_text().strip())
PY
python3 scripts/coord-tools/lean-mcp diag Solidity/Examples/Tactics/OpenLoops.lean
lake build solkeycheck
.lake/build/bin/solkeycheck --key "$SOLKEY_RULES"
