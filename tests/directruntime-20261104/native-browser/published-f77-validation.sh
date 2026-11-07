#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
bash tests/directruntime-20261104/native-browser/hardening-validation.sh
bash tests/directruntime-20261104/native-browser/sort-conformance.sh
