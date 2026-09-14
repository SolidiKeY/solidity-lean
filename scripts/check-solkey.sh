#!/usr/bin/env bash
# Cross-check the sort annotations (TacletAnnotations.lean) against solkey's
# taclet file. The default location is a checkout beside this repository
# (../solkey); override with --key <path> or SOLKEY_RULES. Exit 0 = match or
# no checkout found, 1 = drift, 2 = parse anomaly. See SolkeyCheck.lean.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$repo_root"
export PATH="$repo_root/scripts/lean-vscode/bin:$PATH"

lake build solkeycheck >/dev/null
exec ./.lake/build/bin/solkeycheck "$@"
