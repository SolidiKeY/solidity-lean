#!/usr/bin/env bash
# The optional package owns its dependencies; the core stays independent.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
if ! cmp -s "$repo_root/lean-toolchain" "$repo_root/Bridge/lean-toolchain"; then
  echo "Bridge and core must use the same Lean toolchain." >&2
  exit 1
fi
cd "$repo_root/Bridge"
sha256sum --check vendor/EvmYul/SHA256SUMS
sha256sum --check vendor/Loom/SHA256SUMS
sha256sum --check vendor/CaseStudies/SHA256SUMS
exec lake build
