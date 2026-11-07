#!/usr/bin/env bash
set -euo pipefail
source /emsdk/emsdk_env.sh >/dev/null 2>&1
export EM_CONFIG=/emsdk/.emscripten EMCC_CORES=1 BINARYEN_CORES=1 LEAN_NUM_THREADS=1
export EM_CACHE="$PWD/.lake/native-browser-wasm/direct-toolchain-cache"
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
timeout --kill-after=10s 300s python3 .lake/native-browser-readbounds-6513/stack-symbols.py
