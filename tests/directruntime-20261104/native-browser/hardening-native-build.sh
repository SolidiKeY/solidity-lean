#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=
export CC=/usr/bin/x86_64-linux-gnu-gcc-14
output=${NATIVE_BROWSER_NATIVE_OUTPUT:-$PWD/.lake/native-browser-hardening/native}
if [[ ${NATIVE_BROWSER_REQUIRE_EMPTY:-0} == 1 ]]; then [[ ! -e "$output" ]]; fi
python3 scripts/build-direct-native.py "$PWD/.lake/native-browser-prefix" "$PWD/.lake/native-browser-lean4" "$output"
