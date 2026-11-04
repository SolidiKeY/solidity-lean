#!/usr/bin/env bash
set -euo pipefail
attempt=$NATIVE_BROWSER_WASM_ATTEMPT
for step in gmp compact direct; do
 python3 tests/directruntime-20261104/native-browser/prepare-image-cache.py "docs/benchmarks/directruntime-2026-11-04/before/wasm-$attempt-$step-cache.json"
 case "$step" in
 gmp) command=(bash tests/directruntime-20261104/native-browser/gmp-serial.sh);;
 compact) command=(bash tests/directruntime-20261104/native-browser/compact-runtime-cache.sh);;
 direct) command=(bash web/tools/lean-wasm/build-direct.sh);;
 esac
 python3 tests/directruntime-20261104/native-browser/bounded-command.py "docs/benchmarks/directruntime-2026-11-04/before/wasm-$attempt-$step-gate.json" "${command[@]}"
done
