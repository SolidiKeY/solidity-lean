#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
export SOLIDITY_BROWSER_DIRECT="$PWD/.lake/native-browser-environment/direct"
export SOLIDITY_BROWSER_SOLJSON=/workspace/.setup/solkey/keyext.solidity.core/build/soljson/soljson-v0.8.34+commit.80d5c536.js
unset SOLIDITY_BROWSER_LEAN
node web/tools/build-static.mjs
node web/tools/build-single-file.mjs
