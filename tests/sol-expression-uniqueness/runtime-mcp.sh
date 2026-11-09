#!/usr/bin/env bash
set -euo pipefail
export LEAN_PROJECT_PATH=/workspace/solidity-lean
export LEAN_LSP_MAX_OPEN_FILES=3
export LEAN_MCP_DISABLED_TOOLS=lean_leansearch,lean_loogle,lean_leanfinder,lean_state_search,lean_hammer_premise,lean_get_widgets,lean_get_widget_source
exec /workspace/solidity-lean/.venv/bin/python -m lean_lsp_mcp --lean-project-path /workspace/solidity-lean
