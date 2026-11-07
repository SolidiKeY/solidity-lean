#!/usr/bin/env bash
# The repository is public: tracked files must not carry a person's home
# directory (`/home/<user>/…`, `/Users/<user>/…`). Write `~`, `$XDG_STATE_HOME`,
# `$REPO` or a repository-relative path instead. Container users (`agent`,
# `ubuntu`, `user`, `runner`, `root`) are not people and stay allowed.
set -euo pipefail
cd "$(dirname "$0")/.."

# Generated fixtures whose bytes are pinned elsewhere; drop a line once the
# fixture is regenerated (`scripts/solc-ast.mjs` now writes relative sources).
allow=(
  tests/solc/TestSuite.ast.json  # hashed by `solc_import` in Solidity/Solkey/TestSuite.lean
)

pattern='(^|[^A-Za-z0-9_.~/-])/(home|Users)/(?!(agent|ubuntu|user|runner|root)/)[A-Za-z0-9._-]+/'
excludes=()
for f in "${allow[@]}"; do excludes+=(":(exclude)$f"); done

if hits=$(git grep -naP "$pattern" -- . "${excludes[@]}"); then
  printf '%s\n' "$hits" | cut -c1-200
  echo "private-paths: $(printf '%s\n' "$hits" | wc -l) line(s) with a home directory; use ~, \$XDG_STATE_HOME or a relative path" >&2
  exit 1
fi
echo "private-paths: OK"
