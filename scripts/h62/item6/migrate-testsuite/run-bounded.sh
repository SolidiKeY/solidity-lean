#!/usr/bin/env bash
set -euo pipefail
# Same runtime image digest, resource settings and mounts for both toolchains.
# Invoke from the repository root. Command arguments execute inside the container.
: "${H62_RUNTIME_IMAGE:?set an immutable python runtime image@sha256 digest}"
[[ "$H62_RUNTIME_IMAGE" == *@sha256:* ]] || { echo "immutable runtime image required" >&2; exit 2; }
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock -n 9
[[ "$(git branch --show-current)" == codex/solidity-h62-6-20261106/migrate-testsuite ]]
git status --short
exec env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH \
 docker --host=unix:///var/run/docker.sock run --rm --read-only \
 --name h62-migrate-testsuite-bounded --network none --cap-drop ALL \
 --security-opt no-new-privileges --memory 12g --memory-swap 12g --cpus 4 \
 --user "$(id -u):$(id -g)" --tmpfs /tmp:rw,nosuid,nodev,size=64m \
 --mount type=bind,src=/workspace,dst=/workspace,readonly \
 --mount type=bind,src=/workspace/h62-migrate-testsuite/evidence,dst=/workspace/h62-migrate-testsuite/evidence \
 --mount type=bind,src=/sys/fs/cgroup,dst=/h62-parent-cgroup,readonly \
 --workdir /workspace/solidity-lean -e LEAN_NUM_THREADS=1 -e GIT_OPTIONAL_LOCKS=0 \
 -e H62_RUNTIME_IMAGE="$H62_RUNTIME_IMAGE" \
 -e H62_PARENT_MEMORY_MAX="$(cat /sys/fs/cgroup/memory.max)" \
 -e H62_PARENT_CPU_MAX="$(cat /sys/fs/cgroup/cpu.max)" \
 -e H62_PARENT_SWAP_MAX="$(cat /sys/fs/cgroup/memory.swap.max)" \
 "$H62_RUNTIME_IMAGE" "$@"
