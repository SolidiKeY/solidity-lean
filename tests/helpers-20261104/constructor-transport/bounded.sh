#!/usr/bin/env bash
set -euo pipefail
cd /workspace/solidity-lean
ctor_cid=$(mktemp tests/helpers-20261104/constructor-transport/cid.XXXXXX)
rm "$ctor_cid"
trap 'rm -f "$ctor_cid"' EXIT
docker --host=unix:///var/run/docker.sock run --rm --cidfile "$ctor_cid" --network=none --tmpfs /tmp:rw,nosuid,nodev,size=1g --memory=12g --memory-swap=12g --cpus=1 --user=1000:1000 \
 --mount type=bind,src=/opt/codex,dst=/opt/codex,readonly \
 --mount type=bind,src=/usr,dst=/usr,readonly --mount type=bind,src=/bin,dst=/bin,readonly \
 --mount type=bind,src=/lib,dst=/lib,readonly --mount type=bind,src=/lib64,dst=/lib64,readonly \
 --mount type=bind,src=/etc/alternatives,dst=/etc/alternatives,readonly \
 --mount type=bind,src=/workspace,dst=/workspace --workdir /workspace/solidity-lean \
 constructor-transport-runtime:empty /bin/bash -c '
set -euo pipefail
test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888
test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0
source /workspace/.setup/activate.sh
export PATH=/workspace/solidity-lean/tests/helpers-20261104/constructor-transport/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
export LEAN_NUM_THREADS=1
export HOME=/workspace
exec "$@"' bounded "$@" &
ctor_job=$!
while kill -0 "$ctor_job" 2>/dev/null && [ ! -s "$ctor_cid" ]; do sleep 0.1; done
if [ -s "$ctor_cid" ]; then
  python3 tests/helpers-20261104/constructor-transport/reserve-guard.py "$(cat "$ctor_cid")" &
  ctor_guard=$!
fi
result=0
wait "$ctor_job" || result=$?
if [ -n "${ctor_guard:-}" ]; then wait "$ctor_guard" || result=$?; fi
exit "$result"
