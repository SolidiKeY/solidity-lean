#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= PYTHONDONTWRITEBYTECODE=1
export PATH="$PWD/.lake/native-browser-prefix/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
python3 - <<'CONFIG'
from pathlib import Path
import re,tomllib
s=Path('lakefile.toml').read_text().replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
s=re.sub(r'(\[\[lean_(?:lib|exe)\]\]\nname = "[^"]+"\n)(?!weakLeanArgs)',r'\1weakLeanArgs = ["-j1"]\n',s)
Path('.lake/native-browser-serial.toml').write_text(s)
for group in ['lean_lib','lean_exe']:
 for target in tomllib.loads(s)[group]:assert '-j1' in target['weakLeanArgs']
CONFIG
lake build Solidity.Frontend.ExecutableAst.Memory.Reader Solidity.Frontend.ExecutableAst.ControlTuple.Adapter Solidity.Frontend.ExecutableAst.ControlTuple.AdmissionControls
