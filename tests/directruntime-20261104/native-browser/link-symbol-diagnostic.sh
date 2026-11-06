#!/usr/bin/env bash
set -euo pipefail
source /emsdk/emsdk_env.sh >/dev/null 2>&1
export EM_FROZEN_CACHE=0 EM_CACHE="$PWD/.lake/native-browser-wasm/direct-toolchain-cache"
export EMCC_CORES=1 BINARYEN_CORES=1 LEAN_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
python3 tests/directruntime-20261104/native-browser/link-symbol-diagnostic.py
