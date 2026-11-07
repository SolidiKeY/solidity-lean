#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p /tmp/solidity-lean-feature-groups-20261025
exec flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock \
 timeout 300 docker run --rm --memory=12g --memory-swap=12g --cpus=1 --user=1000:1000 \
 -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro \
 -w /workspace/solidity-lean ubuntu:24.04 bash -c '
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888
test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0
available=$(awk "/MemAvailable:/ {print \$2}" /proc/meminfo)
test "$available" -ge 4194304
lean --version
lake --version
timeout 180 lake env lean -j1 --tstack=131072 Solidity/KeySort.lean
echo KEYSORT_PASS
mkdir -p .lake/build/lib/lean/Solidity/SolcValidation
timeout 180 lake env lean -j1 --tstack=131072 -o .lake/build/lib/lean/Solidity/SolcValidation/Dialect.olean Solidity/SolcValidation/Dialect.lean
timeout 180 lake env lean -j1 --tstack=131072 tests/fullscope-20261104/vt1/DialectChecks.lean
echo DIALECT_INTERFACE_PASS
cat /sys/fs/cgroup/memory.peak
'
