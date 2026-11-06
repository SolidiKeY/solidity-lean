#!/usr/bin/env bash
set -euo pipefail
export BINARYEN_CORES=1
wasm=${1:?Expected the linked Lean Wasm file}
optimizer=${2:-/emsdk/upstream/bin/wasm-opt}
script_hash=$(sha256sum "${BASH_SOURCE[0]}")
tool_version=$("$optimizer" --version)
key=$(printf '%s\n' "${script_hash%% *}" "$tool_version" | sha256sum)
stamp="$wasm.o1-${key%% *}.sha256"
current_hash=$(sha256sum -- "$wasm")
if [[ -f "$stamp" ]] && [[ $(<"$stamp") == "${current_hash%% *}" ]]; then
  echo 'Lean Wasm optimization already verified.'
  exit 0
fi
temporary="$wasm.optimized.tmp"
trap 'rm -f -- "$temporary"' EXIT
"$optimizer" "$wasm" -O1 --enable-tail-call --enable-exception-handling \
  --enable-multivalue --enable-reference-types --enable-bulk-memory \
  --enable-mutable-globals --enable-sign-ext --enable-nontrapping-float-to-int \
  -o "$temporary"
mv -- "$temporary" "$wasm"
optimized_hash=$(sha256sum -- "$wasm")
printf '%s\n' "${optimized_hash%% *}" > "$stamp"
