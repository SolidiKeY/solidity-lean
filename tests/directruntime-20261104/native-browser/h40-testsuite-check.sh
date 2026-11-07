#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= PYTHONDONTWRITEBYTECODE=1
export PATH="$PWD/.lake/native-browser-h40-full-bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
bash scripts/check-testsuite.sh --solkey "$PWD/tests/migration/solkey/keyext.solidity.examples"
