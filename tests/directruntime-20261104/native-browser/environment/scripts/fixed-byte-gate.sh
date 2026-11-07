#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=
export PATH="$PWD/.lake/native-browser-b86a-gate-bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
export GATE_LOGS=/workspace/scratch/browser-chain/environment/fixed-byte-markers
[[ ! -e $GATE_LOGS ]]
bash scripts/coord-tools/gate.sh per-file tests/directruntime-20261104/native-browser/fixed-byte/MarkerControls.lean
