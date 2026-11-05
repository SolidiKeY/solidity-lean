#!/usr/bin/env bash
set -euo pipefail
cd /workspace/solidity-lean
exec flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock \
 docker run --rm --memory=12g --memory-swap=12g --cpus=1 --user=1000:1000 \
 -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro -w /workspace/solidity-lean \
 ubuntu:24.04 bash -c '
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
export PATH="/workspace/solidity-lean/tests/fullscope-20261104/vt1/ImportFollowup/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
exec python3 tests/fullscope-20261104/vt1/ImportFollowup/run.py "$@"
' bash "$@"
