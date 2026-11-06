#!/usr/bin/env bash
set -euo pipefail
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
evidence="${1:?absolute off-git evidence directory required}"
[[ "$evidence" = /* ]] || exit 2
evidence="$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).resolve())' "$evidence")"
case "$evidence/" in "$repo/"*) echo 'bulk evidence must stay outside repository' >&2; exit 2 ;; esac
mkdir -p "$evidence"
cd "$repo"
export PYTHONDONTWRITEBYTECODE=1
python3 tests/h62/item4/generic-internalflow/test_census.py
python3 scripts/h62/item4/generic-internalflow/census.py --revision c6f550e281a7e5affa9a99bc2cdaed556dec00e4 --output "$evidence/original-inventory.json"
python3 scripts/h62/item4/generic-internalflow/census.py --output "$evidence/reproduced-inventory.json" --compare "$evidence/original-inventory.json"
cmp "$evidence/original-inventory.json" "$evidence/reproduced-inventory.json"
python3 tests/h62/item4/generic-internalflow/test_classification.py
python3 scripts/h62/item4/generic-internalflow/classify.py --inventory "$evidence/original-inventory.json" --output "$evidence/semantic-inventory.json"
python3 scripts/h62/item4/generic-internalflow/classify.py --inventory "$evidence/original-inventory.json" --output "$evidence/semantic-inventory-reproduced.json"
cmp "$evidence/semantic-inventory.json" "$evidence/semantic-inventory-reproduced.json"
sha256sum "$evidence/original-inventory.json" "$evidence/reproduced-inventory.json" "$evidence/semantic-inventory.json"
python3 tests/h62/item4/generic-internalflow/test_embedded.py
python3 scripts/h62/item4/generic-internalflow/embedded.py --inventory "$evidence/original-inventory.json" --output "$evidence/embedded-inventory.json"
python3 scripts/h62/item4/generic-internalflow/embedded.py --inventory "$evidence/original-inventory.json" --output "$evidence/embedded-reproduced.json"
cmp "$evidence/embedded-inventory.json" "$evidence/embedded-reproduced.json"
sha256sum "$evidence/embedded-inventory.json"
python3 tests/h62/item4/generic-internalflow/test_prefix.py
python3 scripts/h62/item4/generic-internalflow/prefix.py --inventory "$evidence/original-inventory.json" --output "$evidence/prefix-inventory.json"
python3 scripts/h62/item4/generic-internalflow/prefix.py --inventory "$evidence/original-inventory.json" --output "$evidence/prefix-reproduced.json"
cmp "$evidence/prefix-inventory.json" "$evidence/prefix-reproduced.json"
sha256sum "$evidence/prefix-inventory.json"
git diff --check
printf '%s\n' 'PASS external census/classification acceptance; NOT semantic Lean proof or RUNTIME_GATE_PASS'
