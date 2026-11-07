#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
[[ ! -e web/artifacts/performance-single-report.json ]]
[[ ! -e docs/benchmarks/directruntime-2026-11-04/before/browser-edit-controls.json ]]
trap 'if [[ -f web/artifacts/performance-single-report.json ]]; then cp web/artifacts/performance-single-report.json docs/benchmarks/directruntime-2026-11-04/before/browser-edit-controls.json; fi' EXIT
# Default mode: ordinary checks; cached retrieval and listing are separate controls.
node web/test/performance.cjs --single
