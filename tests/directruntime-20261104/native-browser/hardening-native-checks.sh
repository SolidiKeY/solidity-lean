#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
node tests/directruntime-20261104/native-browser/hardening-native-checks.mjs
python3 tests/directruntime-20261104/native-browser/builder-provenance-tests.py
python3 scripts/test-direct-runtime-closure.py
python3 tests/directruntime-20261104/native-browser/closure-regressions.py
