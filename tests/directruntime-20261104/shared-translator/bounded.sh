#!/usr/bin/env bash
set -euo pipefail
cd "${SHARED_CHECKOUT_ROOT:-/workspace/solidity-lean}"
extra=()
# Lake's MCP dependency workers reopen the root config. Keep their -j1 explicit
# through a container-only read-only overlay; the host checkout is unchanged.
if [[ ${SHARED_MCP_SERIAL_OVERLAY:-0} == 1 ]]; then
  extra=(-v "$PWD/tests/directruntime-20261104/shared-translator/bounded-lakefile.toml:$PWD/lakefile.toml:ro")
fi
exec flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock \
  python3 tests/directruntime-20261104/shared-translator/outer_guard.py \
  env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH \
  docker --host=unix:///var/run/docker.sock run --rm --name "shared-translator-$$" --label codex.task=shared-translator --memory=12g --memory-swap=12g --cpus=1 \
    --user=1000:1000 "${extra[@]}" -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro \
    -w "$PWD" ubuntu:24.04 bash -c '
      set -euo pipefail
      test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888
      test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0
      source /workspace/.setup/activate.sh
      export LEAN_NUM_THREADS=1 LEAN_LSP_MAX_OPEN_FILES=1
      export PATH="/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PWD/tests/directruntime-20261104/shared-translator/bin:$PATH"
      exec python3 tests/directruntime-20261104/shared-translator/measure.py "$@"
    ' bounded "$@"
