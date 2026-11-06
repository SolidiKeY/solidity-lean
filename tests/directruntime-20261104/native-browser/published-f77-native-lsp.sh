#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
export SOLKEY_ROOT=/workspace/.setup/solkey
export SOLIDITY_LEAN_DIRECT_DIR="$PWD/.lake/native-browser-f77/native"
export TESTSUITE_EXTENSION_REPORT="$PWD/docs/benchmarks/directruntime-2026-11-04/published-f77/extension.json"
[[ ! -e "$TESTSUITE_EXTENSION_REPORT" ]]
node vscode/test/measure-testsuite-speed.cjs
