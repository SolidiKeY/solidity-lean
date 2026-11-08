#!/usr/bin/env bash
set -euo pipefail
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
python3 tests/directruntime-20261104/native-browser/readbounds/scripts/capture-selected-c.py
