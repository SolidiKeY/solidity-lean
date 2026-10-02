#!/usr/bin/env bash
# Every backticked `<path>.lean` in the repository's prose must name a file
# that exists.
#
# Docstrings here cite modules by four different conventions, so a reference
# is resolved in this order and the first hit wins:
#
#   1. relative to the citing file's own directory  (`ReadWrite.lean` cited
#                                                     from `Calculus/Close.lean`)
#   2. relative to `Solidity/`                      (`Theory/Storage.lean`)
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
# are not ours to resolve and are listed in EXTERNAL below.
#
# Exit 0 = every reference resolves, 1 = at least one does not.
set -euo pipefail

cd "$(dirname "$0")/.."

strict=0
[ "${1-}" = "--strict" ] && strict=1

# Prefixes naming a file in another repository, plus the one deliberate
# placeholder (`PartNN` stands for Part01..Part11).
EXTERNAL='^(SolKey/|EvmYul/|Decode/)|PartNN'

lean_files=$(git ls-files '*.lean')

missing=0
ambiguous=0

while IFS=$'\t' read -r src ref; do
  [ -z "$ref" ] && continue
  [[ "$ref" =~ $EXTERNAL ]] && continue

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
