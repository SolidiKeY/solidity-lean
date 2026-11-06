#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /emsdk/emsdk_env.sh >/dev/null 2>&1
export EM_CONFIG=/emsdk/.emscripten
export EM_FROZEN_CACHE=0 EM_CACHE="$PWD/.lake/native-browser-wasm/direct-toolchain-cache"
export EMCC_CORES=1 BINARYEN_CORES=1 LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=
export LEAN_WASM_SOURCE=/work/lean4
python3 scripts/build-direct-runtime.py "$PWD/.lake/native-browser-prefix" /work/build64/stage1 "$PWD/.lake/native-browser-f77/direct"
