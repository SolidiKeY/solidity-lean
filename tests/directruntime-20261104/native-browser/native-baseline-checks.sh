#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
export TESTSUITE_BENCH_DIR="$PWD/docs/benchmarks/directruntime-2026-11-04/before/inputs"
[[ ! -e "$TESTSUITE_BENCH_DIR/native.json" ]] || { echo "Refusing timing report overwrite" >&2; exit 64; }
export DIRECT_NATIVE="$PWD/.lake/direct-native/direct-check"
node scripts/testsuite-performance.mjs --reuse --native
node scripts/check-direct-testsuite.mjs
PYTHONDONTWRITEBYTECODE=1 python3 scripts/test-direct-runtime-closure.py
PYTHONDONTWRITEBYTECODE=1 python3 tests/directruntime-20261104/native-browser/closure-regressions.py
