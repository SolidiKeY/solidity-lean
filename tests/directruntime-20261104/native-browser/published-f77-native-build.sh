#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= PYTHONDONTWRITEBYTECODE=1
export PATH="$PWD/.lake/native-browser-prefix/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
lake build Solidity.Frontend.ExecutableAst.Shared.Intrinsic
export NATIVE_BROWSER_NATIVE_OUTPUT="$PWD/.lake/native-browser-f77/native"
export NATIVE_BROWSER_REQUIRE_EMPTY=1
bash tests/directruntime-20261104/native-browser/hardening-native-build.sh
