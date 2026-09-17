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
# Ahead of both: a `lake` that adds `--tstack` to `serve`. The client spawns
# the server as a hardcoded `lake serve --`, so this shim is the only place
# the flag can be added, and without it a file worker on one of the worked
# derivations dies of deep recursion. It holds only `lake`, so `lean` still
# comes from elan.
EXTRA_PATH="$PROJECT_ROOT/scripts/lean-mcp/bin:$EXTRA_PATH"
export PATH="$EXTRA_PATH:$PATH"

# Run from the project root so paths reported by Git and Lean resolve alike.
cd "$PROJECT_ROOT"

# This package has no Mathlib and no external dependencies, so the remote
# Mathlib search tools can never return anything usable here; the widget tools
# are verbose and unused. Dropping their schemas from the tool list saves
# context in every agent session that connects.
export LEAN_MCP_DISABLED_TOOLS="lean_leansearch,lean_loogle,lean_leanfinder,lean_state_search,lean_hammer_premise,lean_get_widgets,lean_get_widget_source"

# Replace the server's generic instruction block with the workflow this
# package actually wants. It is prepended to every session, so keep it short.
export LEAN_MCP_INSTRUCTIONS="Lean 4 package with no Mathlib and no external dependencies; do not suggest Mathlib lemmas. Line/column are 1-indexed. After an edit, run lean_diagnostic_messages on that file alone (interactive=false) rather than a build; lake build costs ~24 min here. Use lean_goal then lean_multi_attempt before writing a tactic. Use lean_local_search to check a name exists before using it. Files are large: use lean_file_outline and ranged reads, never read one whole. Use lean_build only after import or module changes."

exec "$VENV/bin/python" -m lean_lsp_mcp \
  --lean-project-path "$PROJECT_ROOT" "$@"
