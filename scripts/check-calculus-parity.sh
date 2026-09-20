#!/usr/bin/env bash
# Calculus parity press button: elaborate the rule-table corpus
# (Solidity/Corpus/Calculus/*.lean) and compare the
# per-obligation verdicts against tests/solkey/expected-calculus.tsv.
#
# This is the answer to "can the solkey tests be proved from Rules.lean
# alone?", one row at a time. A `proved` row means the taclets drove the
# program to a frontier with nothing left to execute and that frontier
# holds at the contract's store; an `open` row means they did not, and the
# note says where they stopped.
#
#   ./scripts/check-calculus-parity.sh            check against the table
#   ./scripts/check-calculus-parity.sh --update   re-pin it
#
# It is the same runner as the wp corpus's, in --calculus mode: the
# diagnostic attribution and the exit-code caution are the parts that are
# easy to get wrong, and they do not differ between the two.
set -euo pipefail
exec "$(dirname "$0")/check-solkey-parity.sh" --calculus "$@"
