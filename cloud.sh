#!/usr/bin/env bash
# Setup script for a Claude Code cloud environment: solidity-lean
set -euxo pipefail

# Lean toolchain via elan (version comes from lean-toolchain)
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
grep -q '.elan/bin' "$HOME/.bashrc" 2>/dev/null || echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"

# Find the repo checkout
REPO="$(git rev-parse --show-toplevel 2>/dev/null || true)"
if [ -z "$REPO" ] || [ ! -f "$REPO/lakefile.toml" ]; then
  REPO="$(dirname "$(find / -maxdepth 4 -name lakefile.toml -path '*solidity-lean*' 2>/dev/null | head -1)")"
fi
cd "$REPO"

# Install the toolchain pinned in lean-toolchain
elan toolchain install "$(cat lean-toolchain)" || true
lean --version

# solkey checkout beside the repo, for `lake exe solkeycheck` (allowed to fail if private)
if [ ! -d ../solkey ]; then
  git clone --depth 1 https://github.com/SolidiKeY/solkey ../solkey || echo "solkey clone skipped"
fi

# Lean MCP server venv (same pin as scripts/run-lean-mcp.sh)
python3 -m venv .venv
PIP_DISABLE_PIP_VERSION_CHECK=1 .venv/bin/python -m pip install --quiet -r scripts/lean-mcp-requirements.txt

# Cache: build the oleans now so sessions start warm (~24 min cold)
lake build Solidity 2>&1 | tail -n 40
