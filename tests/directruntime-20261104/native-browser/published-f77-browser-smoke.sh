#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
[[ ! -e web/artifacts/single-file-report.json ]]
[[ ! -e docs/benchmarks/directruntime-2026-11-04/published-f77/browser-smoke.json ]]
trap 'if [[ -f web/artifacts/single-file-report.json ]]; then cp web/artifacts/single-file-report.json docs/benchmarks/directruntime-2026-11-04/published-f77/browser-smoke.json; fi' EXIT
node web/test/website.cjs --single --proofs
