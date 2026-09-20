#!/usr/bin/env bash
# The paper-parity table, checked.  `docs/paper-parity.md` has one row per
# worked example of the calculus, and the "Chain" column of a row either names
# the theorem that *is* that example or starts with an em dash and argues why
# there is none.  This script fails when a row names a theorem no source file
# declares -- a rename, a deletion, or a row written ahead of the chain.
#
#   ./scripts/check-paper-parity.sh
#
# Seconds: it greps, it does not elaborate.  What it cannot check is the other
# direction -- that a chain in `Paper/` is in the table -- so it reports the
# chains no row mentions as a warning rather than a failure, since
# `Paper/Checks.lean` and the umbrella carry declarations that are not chains.
set -euo pipefail
cd "$(dirname "$0")/.."

doc=docs/paper-parity.md

# A named chain is written `Module:name` (elsewhere) or `name` (in `Paper/`),
# inside backticks, in the last column of a table row.
named=$(grep -oE '^\| .* \| `[A-Za-z0-9_.]+(:[A-Za-z0-9_]+)?` \|$' "$doc" \
        | sed -E 's/^.*\| `([A-Za-z0-9_.]+(:[A-Za-z0-9_]+)?)` \|$/\1/' || true)

missing=0
for entry in $named; do
  case "$entry" in
    *:*) file="${entry%%:*}"; name="${entry##*:}";
         if ! grep -rqE "(sol_derivation|sol_rewrite|sol_calculus|sol_runs|theorem|example|def) +$name\b" \
              Solidity/Examples/Derivations/"$file".lean \
              Solidity/Counterexamples/"$file".lean 2>/dev/null; then
           echo "missing: $name (expected in $file.lean)"; missing=1
         fi ;;
    *)   if ! grep -rqE "(sol_derivation|sol_rewrite|sol_calculus|sol_runs|theorem|def) +$entry\b" \
              Solidity/Paper/*.lean; then
           echo "missing: $entry (expected in Solidity/Paper/)"; missing=1
         fi ;;
  esac
done

# The other direction, as a warning.
for name in $(grep -hoE '^(sol_derivation|sol_rewrite|sol_calculus) +[A-Za-z0-9_]+' \
                Solidity/Paper/*.lean | awk '{print $2}'); do
  grep -q "\`$name\`" "$doc" || echo "warning: chain \`$name\` is in no row of $doc"
done

if [ "$missing" -ne 0 ]; then
  echo "paper-parity: the table names theorems that do not exist." >&2
  exit 1
fi
echo "paper-parity: every named chain exists."
