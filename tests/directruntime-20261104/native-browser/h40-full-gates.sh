#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= PYTHONDONTWRITEBYTECODE=1
export GATE_BASE=89373e34cdfd6bb5db7054b1c204d01edffc5fa7
export GATE_LOGS="$PWD/docs/benchmarks/directruntime-2026-11-04/h40/full"
mkdir -p .lake/native-browser-h40-full-bin
python3 - <<'CONFIG'
from pathlib import Path
import re,tomllib
p=Path('.lake/native-browser-serial.toml');s=p.read_text()
s=re.sub(r'(\[\[lean_lib\]\]\nname = "[^"]+"\n)(?!weakLeanArgs)',r'\1weakLeanArgs = ["-j1"]\n',s)
p.write_text(s)
c=tomllib.loads(s)
for group in ['lean_lib','lean_exe']:
 for target in c[group]:assert '-j1' in target['weakLeanArgs'],target
CONFIG
cat > .lake/native-browser-h40-full-bin/lake <<'LAKE'
#!/usr/bin/env bash
set -euo pipefail
args=("$@")
for arg in "$@"; do
 if [[ $arg == lean ]]; then args+=(-j1); break; fi
done
exec flock "$PWD/.lake/native-browser-h40-lean-process.lock" /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml "${args[@]}"
LAKE
chmod +x .lake/native-browser-h40-full-bin/lake
export PATH="$PWD/.lake/native-browser-h40-full-bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
bash scripts/coord-tools/gate.sh full
