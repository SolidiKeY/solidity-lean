#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
export SOLKEY_ROOT=/workspace/.setup/solkey
export SOLIDITY_LEAN_DIRECT_DIR="$PWD/.lake/direct-native"
export TESTSUITE_EXTENSION_REPORT="$PWD/docs/benchmarks/directruntime-2026-11-04/before/extension.json"
[[ ! -e "$TESTSUITE_EXTENSION_REPORT" ]]
node vscode/test/measure-testsuite-speed.cjs
