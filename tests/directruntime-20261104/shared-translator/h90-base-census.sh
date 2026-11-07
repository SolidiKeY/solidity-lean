#!/usr/bin/env bash
# Guards H90 base/head parity on the authorized identical78-file set.
set -euo pipefail
cd /workspace/solidity-lean
owned="$PWD/tests/directruntime-20261104/shared-translator"
base=$(cat "$owned/artifacts/h90/measurement-base.txt")
[[ $base =~ ^[0-9a-f]{40}$ ]]
baseline_path="/workspace/solidity-lean-h90-baseline-${base:0:8}"
SHARED_CHECKOUT_ROOT="$baseline_path" SHARED_MCP_SERIAL_OVERLAY=1   bash "$owned/bounded.sh" bash "$owned/h90-census-command.sh"
flock /tmp/solidity-lean-feature-groups-20261025/writer.lock   cp "$baseline_path/tests/directruntime-20261104/shared-translator/artifacts/h90/cr-census-results.json" "$owned/artifacts/h90/base-census-results.json"
