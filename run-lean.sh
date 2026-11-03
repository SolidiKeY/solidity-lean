#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

with_bridge=0
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 1 && "$1" == --bridge ]]; then
    with_bridge=1
  else
    echo "Usage: $0 [--bridge]" >&2
    exit 2
  fi
fi

cd "$repo_root"
# elan first: it reads lean-toolchain (v4.24.0) natively. The lean-vscode nix
# shims only resolve toolchains present in the nix store (4.29.1) and would
# pick the wrong version, so they come after elan.
export PATH="$HOME/.elan/bin:$repo_root/scripts/lean-vscode/bin:$PATH"

# The core reaches no elaborator module (`docs/parallelism.md`): no Lean.
node scripts/check-layers.mjs
# One Lake invocation: the default targets (read from `lakefile.toml`) and
# solkey's TestSuite through the solc import. The TestSuite is not a default
# target, and the import reports a function that stops elaborating as a row,
# so only its pinned report (`#guard_msgs` in Solidity/Solkey/TestSuite.lean)
# catches it. One call lets its chain overlap the default build's tail
# instead of starting after it (`docs/parallelism.md`, P5).
mapfile -t default_targets < <(sed -n 's/^defaultTargets[[:space:]]*=[[:space:]]*\[\(.*\)\][[:space:]]*\(#.*\)\{0,1\}$/\1/p' lakefile.toml | tr ',' '\n' | tr -d " \t\"'" | grep -v '^$' || true)
[[ ${#default_targets[@]} -gt 0 ]] || { echo "run-lean: no defaultTargets in lakefile.toml" >&2; exit 2; }
lake build "${default_targets[@]}" SolkeyTestSuite
if [[ "$with_bridge" -eq 1 ]]; then
  ./scripts/check-bridge.sh
fi
# Keep the sort-annotation table honest against the solkey taclet file:
# drift fails the build. Skipped with a warning when no checkout is beside
# this repository -- see scripts/check-solkey.sh.
exec ./scripts/check-solkey.sh
