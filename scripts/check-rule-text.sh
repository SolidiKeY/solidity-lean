#!/usr/bin/env bash
# The rule lines of `Solidity/Calculus/Core/Rules.lean` are those of
# `Solidity/Calculus/Rules.lean` (`docs/intrinsic.md`, W1 "rules"): for each
# judgement the copy holds, the constructor lines of both are diffed.  Prints
# nothing when they agree; `node scripts/core-rules.mjs` rewrites the copy.
set -euo pipefail
cd "$(dirname "$0")/.."

# The constructor lines of `inductive <name> … where` in a file: every line
# after the header's `where` up to the first one that is not indented.
lines() {
  awk -v name="$2" '
    $0 ~ "^inductive " name " " { head = 1 }
    head && !body { if ($0 ~ /where[[:space:]]*$/) body = 1; next }
    body { if ($0 != "" && $0 !~ /^ /) exit; print }
  ' "$1" | sed -e :a -e '/^\n*$/{$d;N;ba' -e '}'
}

status=0
for j in $(grep -o '^-- BEGIN scripts/core-rules.mjs: [A-Za-z]*' Solidity/Calculus/Core/Rules.lean \
    | awk '{print $NF}'); do
  if ! diff <(lines Solidity/Calculus/Rules.lean "$j") \
      <(lines Solidity/Calculus/Core/Rules.lean "$j") >/tmp/check-rule-text.$$ ; then
    echo "$j: Core/Rules.lean differs from Rules.lean (run node scripts/core-rules.mjs):"
    cat /tmp/check-rule-text.$$
    status=1
  fi
done
rm -f /tmp/check-rule-text.$$
exit $status
