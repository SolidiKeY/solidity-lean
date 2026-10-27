#!/usr/bin/env bash
# Load native code for the existing arithmetic implementation during checks.
# Proofs still go through Lean's kernel; no native_decide or budget changes.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
export LEAN_NUM_THREADS=1
lake build +Solidity.Calculus.LinearDecision:dynlib
python3 - <<'PY'
import json, pathlib, re, sys
suffix = {'linux':'.so', 'darwin':'.dylib', 'win32':'.dll'}.get(sys.platform)
if suffix is None: raise SystemExit('unsupported native library platform: '+sys.platform)
root = pathlib.Path('.')
flags = ['--tstack=131072']
for name in ['Solidity_Calculus_VisitedSet','Solidity_Calculus_LinearDecision']:
    path = root / '.lake/build/lib/lean' / (name+suffix)
    if not path.is_file(): raise SystemExit('native prerequisite missing: '+str(path))
    flags.append('--load-dynlib='+str(path))
config = (root/'lakefile.toml').read_text()
config, count = re.subn(r'weakLeanArgs = \["--tstack=131072"\]',
                        'weakLeanArgs = '+json.dumps(flags), config)
if count != 3: raise SystemExit('unexpected Lake configuration; no native check started')
path = root/'.lake/native-arithmetic/lakefile.toml'
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(config)
PY
if [[ $# == 0 ]]; then set -- build; fi
exec lake -f .lake/native-arithmetic/lakefile.toml "$@"
