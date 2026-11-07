#!/usr/bin/env bash
# Isolated PanicBytes helper/closure diagnostic, never the repository runtime gate.
set -euo pipefail
[[ $# == 0 ]] || { echo "usage: $0" >&2; exit 2; }
root="$(cd "$(dirname "$0")/../../../.." && pwd)"
exec flock -x /tmp/solidity-lean-feature-groups-20261025/writer.lock bash -c '
  set -euo pipefail
  cd "$1"
  git status --short --branch
  test ! -e tests/h62/item1/packet-panic/closure-project-retry/.lake || { echo "isolated cache already exists" >&2; exit 1; }
  flock -n /tmp/solidity-lean-feature-groups-20261025/lean-serial.lock true || { echo "serial Lean lock is held" >&2; exit 1; }
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/packet-panic/prepare_serial_toolchain.py
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/packet-panic/verify_toolchain_layout.py
  compare=/workspace/h62-packet-panic-postmerge-evidence/toolchain-archive-compare-build.log
  rc=0
  tar --compare --zstd -f /workspace/lean-4.35.0-linux.tar.zst -C /workspace/h62-toolchain > "$compare" 2>&1 || rc=$?
  if (( rc > 1 )) || rg -q -v ": (Mode|Uid|Gid) differs$" "$compare"; then
    echo "official archive comparison reported non-metadata differences" >&2
    exit 1
  fi
  echo "archive comparison: no differences other than recorded mode/uid/gid"
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lean --version
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lake --version
  exec /workspace/solidity-lean/.venv/bin/python scripts/h62/item1/packet-panic/mcp_serial_diagnostic.py
' _ "$root"
