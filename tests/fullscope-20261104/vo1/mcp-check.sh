#!/usr/bin/env bash
set -euo pipefail
export PATH="/workspace/solidity-lean/tests/fullscope-20261104/vo1/bin:$PATH"
export LEAN_MCP_SERVER_CMD="/workspace/solidity-lean/.venv/bin/python -m lean_lsp_mcp --lean-project-path /workspace/solidity-lean"
export LEAN_MCP_TIMEOUT=180
export LEAN_MCP_START_WAIT=30
export LEAN_LSP_MAX_OPEN_FILES=1
export LEAN_MCP_SOCKDIR=/tmp
trap 'scripts/coord-tools/lean-mcp stop' EXIT
scripts/coord-tools/lean-mcp diag "$1"
