#!/usr/bin/env bash
set -euo pipefail
[[ $# == 1 ]] || { echo "usage: $0 <repo-relative-lean-file>" >&2; exit 2; }
root="$(cd "$(dirname "$0")/../../../.." && pwd)"
exec flock -x /tmp/solidity-lean-feature-groups-20261025/writer.lock bash -c '
  set -euo pipefail
  cd "$1"
  git status --short --branch
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lean --version
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lake --version
  ulimit -v 12582912
  exec /workspace/solidity-lean/.venv/bin/python scripts/h62/item1/packet-panic/mcp_diagnostics.py "$2"
' _ "$root" "$1"
