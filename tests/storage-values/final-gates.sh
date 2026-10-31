#!/usr/bin/env bash
set -euo pipefail
export LEAN_NUM_THREADS=1
export SOLKEY_ROOT=/workspace/.setup/solkey
export SOLKEY_RULES=/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key
lake() { /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f lakefile.storage-values.toml "$@"; }
export -f lake
./run-lean.sh
