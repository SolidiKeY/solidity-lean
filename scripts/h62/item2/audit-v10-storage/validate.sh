#!/usr/bin/env bash
set -euo pipefail
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p /tmp/solidity-lean-feature-groups-20261025
exec flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 "$script_dir/validate.py" "$@"
