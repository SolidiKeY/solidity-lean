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

# Install the toolchain pinned in lean-toolchain. elan downloads from
# release.lean-lang.org, which the cloud network policy blocks (403), so fall
# back to the same release on GitHub and register it under the pinned name.
TOOLCHAIN="$(tr -d '[:space:]' < lean-toolchain)"   # leanprover/lean4:v4.24.0
if ! elan toolchain list | cut -d" " -f1 | grep -qxF "$TOOLCHAIN"; then
  if ! elan toolchain install "$TOOLCHAIN"; then
    VERSION="${TOOLCHAIN##*:v}"                      # 4.24.0
    case "$(uname -m)" in
      aarch64|arm64) ASSET="lean-$VERSION-linux_aarch64" ;;
      *)             ASSET="lean-$VERSION-linux" ;;
    esac
    DIST="$HOME/.elan/dist"
    mkdir -p "$DIST"
    curl -sSfL -o "$DIST/$ASSET.zip" \
      "https://github.com/leanprover/lean4/releases/download/v$VERSION/$ASSET.zip"
    rm -rf "${DIST:?}/$ASSET"
    unzip -q "$DIST/$ASSET.zip" -d "$DIST"
    rm -f "$DIST/$ASSET.zip"
    elan toolchain link "$TOOLCHAIN" "$DIST/$ASSET"
  fi
fi
lean --version
lake --version

# solkey checkout beside the repo, for `lake exe solkeycheck` (allowed to fail if private)
if [ ! -d ../solkey ]; then
  GIT_TERMINAL_PROMPT=0 git clone --depth 1 https://github.com/SolidiKeY/solkey ../solkey \
    || echo "solkey clone skipped"
fi

# Lean MCP server venv (same pin as scripts/run-lean-mcp.sh)
python3 -m venv .venv
PIP_DISABLE_PIP_VERSION_CHECK=1 .venv/bin/python -m pip install --quiet -r scripts/lean-mcp-requirements.txt

# No `lake build` here: setup is cut off after about five minutes and a cold
# `lake build Solidity` takes about 24, so the session fails to start.
