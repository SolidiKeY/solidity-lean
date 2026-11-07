#!/usr/bin/env bash
# Run inside the pinned Emscripten image, with repository, work and native
# prefix mounted at their original absolute paths so Lake artifacts stay valid.
set -euo pipefail
source /emsdk/emsdk_env.sh >/dev/null 2>&1
# The pinned image owns this config; SDK activation alone need not export it.
export EM_CONFIG=/emsdk/.emscripten
[[ -f "$EM_CONFIG" ]] || { echo "Missing pinned SDK config: $EM_CONFIG" >&2; exit 1; }
export PATH="$NATIVE_LEAN_PREFIX/bin:$PATH"
export EMCC_CORES=1 BINARYEN_CORES=1 LEAN_NUM_THREADS=1
export EM_FROZEN_CACHE=0
export EM_CACHE="$LEAN_BROWSER_WORK/direct-toolchain-cache"
export XDG_CACHE_HOME="$LEAN_BROWSER_WORK/direct-native-cache"
export GIT_CONFIG_COUNT=3
export GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0="$LEAN_BROWSER_WORK/lean4"
export GIT_CONFIG_KEY_1=safe.directory GIT_CONFIG_VALUE_1="$PWD"
export GIT_CONFIG_KEY_2=safe.directory GIT_CONFIG_VALUE_2="$(realpath "${LEAN_WASM_SOURCE:-/work/lean4}")"
python3 scripts/build-direct-runtime.py "$NATIVE_LEAN_PREFIX" \
  "$LEAN_BROWSER_WORK/build64/stage1" "$LEAN_BROWSER_WORK/direct"
chmod -R a+rX "$LEAN_BROWSER_WORK/direct"
