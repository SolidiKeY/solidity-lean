#!/usr/bin/env bash
# Every backticked `<path>.lean` in the repository's prose must name a file
# that exists.
#
# Docstrings here cite modules by four different conventions, so a reference
# is resolved in this order and the first hit wins:
#
#   1. relative to the citing file's own directory  (`ReadWrite.lean` cited
#                                                     from `Calculus/Close.lean`)
#   2. relative to `Solidity/`                      (`Theory/Typed/Obs.lean`)
#   3. relative to the repository root              (`Solidity/AST.lean`)
#   4. by unique basename anywhere in the package   (`KeyTaclets.lean` cited
#                                                     from `Examples/Tactics/Values.lean`,
#                                                     which is not in `Calculus/`)
#
# A basename that matches more than one file resolves, but is reported with
# --strict: it is the hazard this repository is most prone to, since the
# reader cannot tell which file is meant either.
#
# References into the sibling repositories (`SolKey/`, `EvmYul/`, `Decode/`)
# and into Mathlib (cited as attribution; only `Bridge/` depends on it) are not
# ours to resolve and are listed in EXTERNAL below, as is the deliberate
# placeholder `PartNN` (Part01..Part11). The two module names the TF-gate
# fixture (tests/terra-20261103/gate/test_cases.py) uses inside its disposable
# repositories, Solidity/A and Solidity/MissingFixture, are exempt
# only when that fixture file cites them (FIXTURE_SRC/FIXTURE_REF). Captured tool output
# (`*.log`, `*validation.json` records) is skipped: it quotes earlier runs
# verbatim, including their findings.
#
# Exit 0 = every reference resolves, 1 = at least one does not.
set -euo pipefail

cd "$(dirname "$0")/.."

strict=0
[ "${1-}" = "--strict" ] && strict=1

# Prefixes naming a file in another repository, plus the deliberate
# placeholder (`PartNN` stands for Part01..Part11).
EXTERNAL='^(SolKey/|EvmYul/|Decode/|Mathlib/)|PartNN'
# The TF-gate fixture's two placeholders, exempt only where that fixture cites
# them: a document elsewhere naming either is still a finding (the fixture's own
# negative control relies on this).
FIXTURE_SRC='^tests/terra-20261103/gate/test_cases\.py$'
FIXTURE_REF='^Solidity/(A|MissingFixture)\.lean$'
CAPTURED='(\.log|validation\.json)$'

# H112: exact source/reference pairs from historical proposals or fixtures.
# No basename or directory-wide exemption: another source citing one still fails.
declare -A HISTORICAL=(
  ["docs/feature-work/h62-1-infer-helpers.md:Solidity/Source/InferHelpers.lean"]="Historical unadopted migration destination; the existing candidate is tests/h62/item1/infer-helpers/Shared.lean."
  ["docs/feature-work/h62-6-migrate-theory.md:StringApiWitness.original-unproved.lean"]="Historical failed experiment retained off git; explicitly excluded from accepted coverage."
  ["scripts/h62/item2/audit-abi-world/test_census.py:Backend/A.lean"]="Synthetic duplicate-row input in a negative census fixture, not a production module."
  ["tests/h62/item4/generic-structuredflow/registration.md:Backend/StructuredFlow/GenericMapped.lean"]="Historical proposed registration destination, never adopted; candidate remains under tests/h62/item4/generic-structuredflow."
  ["tests/h62/item4/generic-structuredflow/registration.md:Solidity/Backend/StructuredFlow/GenericMapped.lean"]="Historical proposed module move, never adopted; no production module existence is claimed."
)

lean_files=$(git ls-files '*.lean')

missing=0
ambiguous=0

while IFS=$'\t' read -r src ref; do
  [ -z "$ref" ] && continue
  [[ "$ref" =~ $EXTERNAL ]] && continue
  [[ "$src" =~ $FIXTURE_SRC && "$ref" =~ $FIXTURE_REF ]] && continue
  [[ "$src" =~ $CAPTURED ]] && continue
  if [ -n "${HISTORICAL["$src:$ref"]-}" ]; then
    echo "historical: $src cites \`$ref\`: ${HISTORICAL["$src:$ref"]}"
    continue
  fi

  dir=$(dirname "$src")
  if [ -f "$dir/$ref" ] || [ -f "Solidity/$ref" ] || [ -f "$ref" ]; then
    continue
  fi

  hits=$(printf '%s\n' "$lean_files" | grep -c -- "\(^\|/\)${ref}\$" || true)
  if [ "$hits" -eq 0 ]; then
    echo "missing:   $src cites \`$ref\`"
    missing=$((missing + 1))
  elif [ "$hits" -gt 1 ]; then
    echo "ambiguous: $src cites \`$ref\` ($hits files share that name)"
    ambiguous=$((ambiguous + 1))
  fi
done < <(
  git ls-files -z \
    | xargs -0 grep -o -n '`[A-Za-z][A-Za-z0-9_/.-]*\.lean`' \
    | sed 's/`//g' \
    | awk -F: '{print $1"\t"$3}' \
    | sort -u
)

if [ "$missing" -gt 0 ]; then
  echo
  echo "FAIL: $missing reference(s) name a file that does not exist."
  exit 1
fi

if [ "$ambiguous" -gt 0 ]; then
  echo
  echo "$ambiguous ambiguous reference(s); all resolve, none is unique."
  [ "$strict" -eq 1 ] && exit 1
fi

echo "OK: every backticked *.lean reference resolves."
