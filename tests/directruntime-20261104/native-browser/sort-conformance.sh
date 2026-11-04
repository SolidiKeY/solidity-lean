#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=
export PATH="$PWD/.lake/native-browser-prefix/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
python3 - <<'PY'
from pathlib import Path
import re
p=Path('.lake/native-browser-serial.toml')
s=p.read_text()
s=re.sub(r'(\[\[lean_exe\]\]\nname = "[^"]+"\n)(?!weakLeanArgs)',r'\1weakLeanArgs = ["--tstack=131072", "-j1"]\n',s)
p.write_text(s)
PY
bash scripts/check-solkey.sh --key "$SOLKEY_RULES"
