#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == --compact-only ]]; then
  exec bash "$(dirname "${BASH_SOURCE[0]}")/build-compact-browser.sh"
fi
repository=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
work=${LEAN_BROWSER_WORK:-"$repository/web/.lean-browser-build"}
native=${LEAN_BROWSER_NATIVE_PREFIX:-$(lean --print-prefix)}
image=${LEAN_BROWSER_BUILD_IMAGE:-solidity-lean-wasm-build:4.24}
mkdir -p "$work"
work=$(cd "$work" && pwd)
native=$(cd "$native" && pwd)
"$native/bin/lean" --version | grep -F 'version 4.24.0,' >/dev/null
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
bash "$repository/web/tools/lean-wasm/test-replace.sh" "$work/lean4" "$native" "$work"

cd "$repository"
LEAN_NUM_THREADS=1 lake build Solidity.Tools.DirectRuntime
LEAN_NUM_THREADS=1 "$native/bin/lean" -j1 --tstack=131072 \
  -o "$work/BrowserFrontend.olean" -c "$work/BrowserFrontend.c" web/browser/BrowserFrontend.lean
LEAN_NUM_THREADS=1 "$native/bin/lean" -j1 --run web/tools/lean-wasm/ImportGraph.lean "$native/src/lean" "$repository" > "$work/import-graph.json"
cp web/tools/lean-wasm/build-runtime.sh "$work/build-lean.sh"
cp web/tools/lean-wasm/build-gmp.sh "$work/build-gmp.sh"
cp web/tools/lean-wasm/internalize-runner.py "$work/internalize-runner.py"
cp web/tools/lean-wasm/optimize-runtime.py "$work/optimize-runtime.py"
cp web/tools/lean-wasm/optimize-wasm.sh "$work/optimize-wasm.sh"
build_args=()
run_args=()
if [[ -n ${LEAN_BROWSER_CA_FILE:-} ]]; then
  build_args+=(--secret "id=system_ca,src=$LEAN_BROWSER_CA_FILE")
  run_args+=(--mount "type=bind,src=$LEAN_BROWSER_CA_FILE,dst=/run/system-ca.pem,readonly")
fi
docker build "${build_args[@]}" -t "$image" web/tools/lean-wasm
container_args=(--rm --memory=4g --memory-swap=4g --cpus=4
  --mount "type=bind,src=$work,dst=/work"
  --mount "type=bind,src=$native,dst=/native,readonly"
  --mount "type=bind,src=$repository/web/browser,dst=/browser,readonly")
docker run "${container_args[@]}" "${run_args[@]}" "$image" bash /work/build-gmp.sh
docker run "${container_args[@]}" "${run_args[@]}" "$image" bash /work/build-lean.sh
docker run "${container_args[@]}" "$image" chmod -R a+rX /work/build64
# Compile the compact verifier from the same generated C/runtime before the
# serialized general-frontend assets are packaged. The SDK stays in Docker.
docker run --rm --memory=4g --memory-swap=4g --cpus=2 --user "$(id -u):$(id -g)" \
  --mount "type=bind,src=$repository,dst=$repository" \
  --mount "type=bind,src=$work,dst=$work" \
  --mount "type=bind,src=$native,dst=$native,readonly" \
  --workdir "$repository" \
  --env "NATIVE_LEAN_PREFIX=$native" --env "LEAN_BROWSER_WORK=$work" \
  "$image" bash "$repository/web/tools/lean-wasm/build-direct.sh"
SOLIDITY_BROWSER_IMPORT_GRAPH="$work/import-graph.json" node web/tools/package-lean.mjs "$work/build64/stage1" "$native" "$work/assets"
printf 'Lean website assets: %s\nBuild the website with SOLIDITY_BROWSER_LEAN=%q SOLIDITY_BROWSER_DIRECT=%q npm run build --prefix web\n' "$work/assets" "$work/assets" "$work/direct"
