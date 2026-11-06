#!/usr/bin/env bash
# Private bounded launcher: keep the explicit -j1 Lake wrapper first on PATH.
set -euo pipefail
project="$(cd "$(dirname "$0")/../../.." && pwd)"
export LEAN_NUM_THREADS=1
export LEAN_LSP_MAX_OPEN_FILES=1
export PATH="$project/tests/sol-numeric-literals/runtime/bin:$PATH"
exec "$project/.venv/bin/python" -m lean_lsp_mcp --lean-project-path "$project" "$@"
