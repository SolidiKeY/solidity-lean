#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
node tests/directruntime-20261104/native-browser/published-8495-controls.mjs
