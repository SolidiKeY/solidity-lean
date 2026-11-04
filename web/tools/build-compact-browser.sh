#!/usr/bin/env bash
set -euo pipefail
repository=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
work=${LEAN_BROWSER_WORK:-"$repository/web/.lean-browser-build"}
native=${LEAN_BROWSER_NATIVE_PREFIX:-$(lean --print-prefix)}
image=${LEAN_BROWSER_BUILD_IMAGE:-solidity-lean-wasm-build:4.24}
mkdir -p "$work"
work=$(cd "$work" && pwd)
native=$(cd "$native" && pwd)
[[ $("$native/bin/lean" --githash) == 797c613eb9b6d4ec95db23e3e00af9ac6657f24b ]]
if [[ ! -d "$work/lean4/.git" ]]; then git clone --depth 1 --branch v4.24.0 https://github.com/leanprover/lean4.git "$work/lean4"; fi
[[ $(git -C "$work/lean4" rev-parse HEAD) == 797c613eb9b6d4ec95db23e3e00af9ac6657f24b ]]
if git -C "$work/lean4" apply --check "$repository/web/tools/lean-wasm/lean-4.24-browser.patch"; then
  git -C "$work/lean4" apply "$repository/web/tools/lean-wasm/lean-4.24-browser.patch"
else
  git -C "$work/lean4" apply --reverse --check "$repository/web/tools/lean-wasm/lean-4.24-browser.patch"
fi
if [[ ! -d "$work/gmp/.git" ]]; then git clone --depth 1 --branch v6.2.1 https://github.com/alisw/GMP.git "$work/gmp"; fi
[[ $(git -C "$work/gmp" rev-parse HEAD) == 2bbd52703e5af82509773264bfbd20ff8464804f ]]
build_args=();run_args=()
if [[ -n ${LEAN_BROWSER_CA_FILE:-} ]]; then
  build_args+=(--secret "id=system_ca,src=$LEAN_BROWSER_CA_FILE")
  run_args+=(--mount "type=bind,src=$LEAN_BROWSER_CA_FILE,dst=/run/system-ca.pem,readonly")
fi
docker build "${build_args[@]}" -t "$image" "$repository/web/tools/lean-wasm"
mounts=(--mount "type=bind,src=$work,dst=/work"
  --mount "type=bind,src=$work,dst=$work"
  --mount "type=bind,src=$(cd "$work/lean4" && pwd -P),dst=/work/lean4"
  --mount "type=bind,src=$native,dst=/native,readonly"
  --mount "type=bind,src=$native,dst=$native,readonly"
  --mount "type=bind,src=$repository,dst=$repository")
for script in build-gmp.sh build-compact-runtime.sh; do
  docker run --rm --memory=1g --memory-swap=1g --cpus=1 "${mounts[@]}" "${run_args[@]}" \
    "$image" bash "$repository/web/tools/lean-wasm/$script"
done
# The native frontend's C has already been built by the caller. This step
# extracts only the reachable pure closure and links it against leanrt.
docker run --rm --memory=4g --memory-swap=4g --cpus=1 "${mounts[@]}" "${run_args[@]}" \
  --workdir "$repository" --env "NATIVE_LEAN_PREFIX=$native" --env "LEAN_BROWSER_WORK=$work" \
  --env LEAN_WASM_SOURCE=/work/lean4 "$image" bash "$repository/web/tools/lean-wasm/build-direct.sh"
docker run --rm --memory=256m --memory-swap=256m "${mounts[@]}" "$image" \
  chmod -R a+rX /work/direct
printf 'Compact generated-C browser verifier: %s\n' "$work/direct"
