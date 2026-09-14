#!/usr/bin/env bash
# Portable wrapper for the lean-lsp-mcp server.
# Resolves paths relative to the project root so .mcp.json
# does not need hardcoded absolute paths.

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# Ensure the venv and package exist
VENV="$PROJECT_ROOT/.venv"
REQUIREMENTS="$PROJECT_ROOT/scripts/lean-mcp-requirements.txt"
if [ ! -x "$VENV/bin/python" ]; then
  python3 -m venv "$VENV"
fi
if ! "$VENV/bin/python" -c \
  "import importlib.metadata as m; raise SystemExit(m.version('lean-lsp-mcp') != '0.29.0')" \
  2>/dev/null; then
  PIP_DISABLE_PIP_VERSION_CHECK=1 \
    "$VENV/bin/python" -m pip install --quiet --requirement "$REQUIREMENTS"
fi

export LEAN_PROJECT_PATH="$PROJECT_ROOT"

# Build a PATH that includes elan, the repo's lean-vscode shims,
# and the standard system directories. elan must come first: it honors
# lean-toolchain (v4.24.0), while the shims only resolve nix-store toolchains.
EXTRA_PATH="$PROJECT_ROOT/scripts/lean-vscode/bin"
[ -d "$HOME/.elan/bin" ] && EXTRA_PATH="$HOME/.elan/bin:$EXTRA_PATH"
export PATH="$EXTRA_PATH:$PATH"

# Run from the project root so paths reported by Git and Lean resolve alike.
cd "$PROJECT_ROOT"

exec "$VENV/bin/python" -m lean_lsp_mcp \
  --lean-project-path "$PROJECT_ROOT" "$@"
