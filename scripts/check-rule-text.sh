#!/usr/bin/env bash
# The rule lines of `Solidity/Calculus/Core/Rules.lean` are those of
# `Solidity/Calculus/Rules.lean` (`docs/intrinsic.md`, W1 "rules"): for each
# judgement the copy holds, every constructor's docstring and `dl{ … }` line
# are compared, the binders before the line aside; then the whole copy,
# binders and side conditions too, against what the script writes (`--check`).
# Prints nothing when they agree; `node scripts/core-rules.mjs` rewrites the copy.
set -euo pipefail
cd "$(dirname "$0")/.."
node scripts/core-rules.mjs --diff
node scripts/core-rules.mjs --check
