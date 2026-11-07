#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]] || { echo "Run via bounded-command.py" >&2; exit 64; }
[[ $(cat /sys/fs/cgroup/memory.max) == 12884901888 ]]
[[ $(cat /sys/fs/cgroup/memory.swap.max) == 0 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
export CC=/usr/bin/x86_64-linux-gnu-gcc-14
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
python3 - <<'SETUP'
from pathlib import Path
root=Path.cwd()
real=Path('/workspace/.setup/tools/lean-4.24.0-linux')
prefix=root/'.lake/native-browser-prefix'
(prefix/'bin').mkdir(parents=True,exist_ok=True)
for child in real.iterdir():
 if child.name!='bin' and not (prefix/child.name).exists(): (prefix/child.name).symlink_to(child)
for child in (real/'bin').iterdir():
 if child.name!='lake' and not (prefix/'bin'/child.name).exists(): (prefix/'bin'/child.name).symlink_to(child)
config=root/'.lake/native-browser-serial.toml'
config.write_text((root/'lakefile.toml').read_text().replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]'))
shim=prefix/'bin/lake'
shim.write_text('#!/usr/bin/env bash\nexec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml "$@"\n')
shim.chmod(0o755)
SETUP
python3 scripts/build-direct-native.py "$PWD/.lake/native-browser-prefix" "$PWD/.lake/native-browser-lean4" "$PWD/.lake/direct-native"
