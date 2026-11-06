#!/usr/bin/env bash
# Synthetic Linux/Docker containment control; no Lean and no production receipt.
set -euo pipefail
if [ "$#" -ne 1 ] || [[ "$1" != /* ]]; then
  printf "usage: %s ABSOLUTE_EMPTY_EVIDENCE_DIRECTORY\n" "$0" >&2
  exit 2
fi
out=$1
mkdir -p "$out"
if [ -n "$(ls -A "$out")" ]; then
  printf "evidence directory must be empty\n" >&2
  exit 1
fi
mkdir "$out/rootfs"
cat > "$out/fixture.c" <<"C"
#include <unistd.h>
#include <stdlib.h>
#include <sys/types.h>
int main(void) {
  pid_t child = fork();
  if (child < 0) return 2;
  if (child == 0) { if (setsid() < 0) _exit(3); sleep(30); _exit(0); }
  sleep(30);
  return 0;
}
C
cc -static -O2 "$out/fixture.c" -o "$out/rootfs/fixture"
docker_local() { env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock "$@"; }
tag="h55-module-times-fixture-${RANDOM}-${RANDOM}:local"
container_id=
nonce=$(python3 -c "import secrets; print(secrets.token_hex(16))")
image_created=0
if docker_local image inspect "$tag" >/dev/null 2>&1; then
  printf "fixture image tag already exists; refusing to alter it\n" >&2
  exit 1
fi
cleanup() {
  if [ -n "$container_id" ]; then docker_local rm -f "$container_id" >/dev/null 2>&1 || true; fi
  if [ "$image_created" = 1 ]; then docker_local image rm "$tag" >/dev/null 2>&1 || true; fi
}
trap cleanup EXIT
tar -C "$out/rootfs" -cf - fixture | docker_local import --change 'ENTRYPOINT ["/fixture"]' - "$tag" > "$out/image-id.txt"
image_created=1
container_id=$(docker_local create --label "org.solidity-lean.h55-fixture=$nonce" --network none --memory 64m --memory-swap 64m --pids-limit 16 --cpus 1 --read-only "$tag")
docker_local start "$container_id" >/dev/null
docker_local inspect --format 'memory={{.HostConfig.Memory}} swap={{.HostConfig.MemorySwap}} network={{.HostConfig.NetworkMode}} pids={{.HostConfig.PidsLimit}}' "$container_id" > "$out/inspect.txt"
test "$(cat "$out/inspect.txt")" = "memory=67108864 swap=67108864 network=none pids=16"
for attempt in {1..30}; do
  docker_local top "$container_id" -eo pid,ppid,pgid,sid,args > "$out/processes.txt"
  if [ "$(wc -l < "$out/processes.txt")" -eq 3 ]; then break; fi
  sleep 0.05
done
[ "$(wc -l < "$out/processes.txt")" -eq 3 ]
read -r parent child < <(awk 'NR==2 {p=$1} NR==3 {print p,$1}' "$out/processes.txt")
[ "$(awk 'NR==2 {print $4}' "$out/processes.txt")" != "$(awk 'NR==3 {print $4}' "$out/processes.txt")" ]
cat "/proc/$parent/cgroup" > "$out/process-cgroup.txt"
cgroup_path=$(sed -n "s/^0:://p" "$out/process-cgroup.txt")
# This executor exposes the daemon container as a sibling in the cgroup
# namespace. Accept only its exact owned ID and the observed mount root.
test "$cgroup_path" = "/../docker/$container_id"
awk '$4 == "/.." && $5 == "/sys/fs/cgroup" && $0 ~ / - cgroup2 / { found=1 } END { exit !found }' /proc/self/mountinfo
cgroup_dir=$(readlink -e "/sys/fs/cgroup/docker/$container_id")
test "$cgroup_dir" = "/sys/fs/cgroup/docker/$container_id"
printf "memory.max=%s memory.swap.max=%s\n" "$(cat "$cgroup_dir/memory.max")" "$(cat "$cgroup_dir/memory.swap.max")" > "$out/effective-cgroup.txt"
test "$(cat "$out/effective-cgroup.txt")" = "memory.max=67108864 memory.swap.max=0"
parent_start=$(awk '{print $22}' "/proc/$parent/stat")
child_start=$(awk '{print $22}' "/proc/$child/stat")
printf "parent=%s start=%s child=%s start=%s\n" "$parent" "$parent_start" "$child" "$child_start" > "$out/identities.txt"
PYTHONDONTWRITEBYTECODE=1 python3 tests/h55/module-times/watch_fixture.py "$container_id" "$nonce" > "$out/watch.json"
docker_local inspect --format 'running={{.State.Running}} exit={{.State.ExitCode}} oom={{.State.OOMKilled}}' "$container_id" > "$out/stopped.txt"
test "$(cat "$out/stopped.txt")" = "running=false exit=137 oom=false"
for attempt in {1..30}; do
  parent_now=$(awk '{print $22}' "/proc/$parent/stat" 2>/dev/null || true)
  child_now=$(awk '{print $22}' "/proc/$child/stat" 2>/dev/null || true)
  if [ "$parent_now" != "$parent_start" ] && [ "$child_now" != "$child_start" ]; then break; fi
  sleep 0.05
done
[ "$parent_now" != "$parent_start" ] && [ "$child_now" != "$child_start" ]
printf "both original process identities absent after automatic deadline cleanup\n" > "$out/cleanup.txt"
printf "PASS: isolated synthetic deadline and containment control (no Lean, no timing receipt)\n"
