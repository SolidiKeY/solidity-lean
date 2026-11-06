#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
/workspace/.setup/tools/lean-4.24.0-linux/bin/lean --version
/workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version
python3 tests/directruntime-20261104/native-browser/builder-provenance-tests.py
python3 scripts/test-direct-runtime-closure.py
python3 tests/directruntime-20261104/native-browser/closure-regressions.py
python3 - <<'CHECK'
import ast,pathlib,subprocess
p=pathlib.Path('tests/directruntime-20261104/native-browser')
for f in list(p.rglob('*.py'))+[pathlib.Path(n) for n in ['scripts/build-direct-native.py','scripts/build-direct-runtime.py','scripts/direct-runtime-closure.py']]:ast.parse(f.read_text(),filename=str(f))
for f in p.glob('*.sh'):subprocess.run(['bash','-n',str(f)],check=True)
for f in list(p.glob('*.mjs'))+list(p.glob('*.cjs')):subprocess.run(['node','--check',str(f)],check=True)
print('PASS Python AST, Bash and Node syntax')
CHECK
