#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]] || { echo "Run via bounded-command.py" >&2; exit 64; }
[[ $(cat /sys/fs/cgroup/memory.max) == 12884901888 ]]
[[ $(cat /sys/fs/cgroup/memory.swap.max) == 0 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
# The coordinator toolkit invokes this shim for a per-file check.
mkdir -p .lake/native-browser-bin
cat > .lake/native-browser-bin/lake <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]] || { echo "Run via bounded-command.py" >&2; exit 64; }
if [[ "$1" == env && "$2" == lean ]]; then
 shift 2
 exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake env lean -j1 "$@"
fi
exit 64
SHIM
chmod +x .lake/native-browser-bin/lake
export PATH="$PWD/.lake/native-browser-bin:$PATH"
export GATE_LOGS="$PWD/docs/benchmarks/directruntime-2026-11-04/setup/keys"
bash scripts/coord-tools/gate.sh per-file Solidity/KeySort.lean
