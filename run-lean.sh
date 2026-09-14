#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

cd "$repo_root"
# elan first: it reads lean-toolchain (v4.24.0) natively. The lean-vscode nix
# shims only resolve toolchains present in the nix store (4.29.1) and would
# pick the wrong version, so they come after elan.
export PATH="$HOME/.elan/bin:$repo_root/scripts/lean-vscode/bin:$PATH"

lake build
# Keep the sort-annotation table honest against the solkey taclet file:
# drift fails the build. Skipped with a warning when no checkout is beside
# this repository -- see scripts/check-solkey.sh.
exec ./scripts/check-solkey.sh
