#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
python3 - <<'PY'
from pathlib import Path
import hashlib,json
root=Path.cwd();target=root/'.lake/testsuite-performance/inputs.json'
expected=root/'docs/benchmarks/directruntime-2026-11-04/before/inputs/inputs.json'
assert not (root/'.lake/testsuite-performance/browser.json').exists(), 'Refusing old browser report'
assert not (root/'docs/benchmarks/directruntime-2026-11-04/before/browser.json').exists()
ident=json.loads((expected.parent/'harness-identities.json').read_text())
p=root/'web/test/testsuite-performance.cjs'
assert hashlib.sha256(p.read_bytes()).hexdigest()==ident['web/test/testsuite-performance.cjs']
if target.exists() or target.is_symlink():
 assert target.read_bytes()==expected.read_bytes(), 'Unexpected harness input preserved'
else:
 target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(expected)
Path('.lake/native-browser-chromium-config').mkdir(exist_ok=True)
Path('.lake/native-browser-chromium-cache').mkdir(exist_ok=True)
PY
trap 'if [[ -f .lake/testsuite-performance/browser.json ]]; then cp .lake/testsuite-performance/browser.json docs/benchmarks/directruntime-2026-11-04/before/browser.json; fi' EXIT
node web/test/testsuite-performance.cjs
