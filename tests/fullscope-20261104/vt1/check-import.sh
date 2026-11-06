#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p /tmp/solidity-lean-feature-groups-20261025
exec flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock \
 timeout 300 docker run --rm --memory=12g --memory-swap=12g --cpus=1 --user=1000:1000 \
 -e VT1_EVIDENCE_STAMP="${VT1_EVIDENCE_STAMP:-}" -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro \
 -w /workspace/solidity-lean ubuntu:24.04 bash -c '
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
exec python3 tests/fullscope-20261104/vt1/measured-checks.py
'
