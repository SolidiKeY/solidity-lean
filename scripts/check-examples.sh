#!/usr/bin/env bash
# Press button for the worked derivations: elaborate every worked example of
# the calculus as a `sol_derivation` chain
# (`Solidity/Examples/Derivations/Paper.lean`).
#
#   ./scripts/check-examples.sh
#
# About 7 minutes of CPU: ~65 derivations over ~390 pinned rule
# applications, each paying its own `simp`+`decide`. That
# is why the module has its own target rather than sitting in
# `Solidity.lean` -- see the comment in
# `SolidityExamples.lean`.
#
# It was 8x that until the two costs a pinned step used to pay went away:
# `rule_simp` reducing `AST.lean`'s string-keyed tables (`name_table_simp`,
# `Examples/SimpAttr.lean`) and the positional walk over `ruleNames` that
# every `.both` step took (`UniquenessAux.firstStepCase_both`). A chain that
# is slow again is one of those two: an identifier with no table arm, or a
# statement a twin pair covers.
#
# A failure here means the derivations and the calculus have drifted apart:
# either a rule was renamed, or its residual changed, or a rule that used to
# fire on one of these programs no longer does. The rule sequences are not
# written down -- `sol_runs`/`steps!` ask `UniquenessAux.candidate` at
# elaboration time -- so there is nothing to re-derive: the failure names the
# statement and the rule it tried. `set_option trace.solidity.steps true in`
# above the offending command prints the sequence it found.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PWD/scripts/lean-vscode/bin:$PATH"

exec lake build SolidityExamples
