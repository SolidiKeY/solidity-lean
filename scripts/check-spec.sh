#!/usr/bin/env bash
# Press button for the SolSpec layer: build the assertion module, the
# `sol_spec` tactic, and the worked obligations of
# `Solidity/Spec/Examples.lean`.
#
#   ./scripts/check-spec.sh            build the whole SoliditySpec lib
#   ./scripts/check-spec.sh --tactic   build only Assertion + Tactic
#                                      (what the VS Code extension needs)
#
# The examples are the reference output of the code generator
# (`vscode-extension/src/spec/emitLean.ts`): they are written by hand in
# exactly the shape it emits, so a green run here means a generated
# obligation file elaborates too.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PWD/scripts/lean-vscode/bin:$PATH"

if [ "${1:-}" = "--tactic" ]; then
  exec lake build Solidity.Spec.Tactic
fi

exec lake build SoliditySpec
