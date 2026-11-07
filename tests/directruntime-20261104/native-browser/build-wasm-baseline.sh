#!/usr/bin/env bash
set -euo pipefail
repository=$(pwd -P)
work="$repository/.lake/native-browser-wasm"
image=solidity-lean-native-browser-wasm:4.24
attempt=${NATIVE_BROWSER_WASM_ATTEMPT:-before-1}
[[ $attempt =~ ^[A-Za-z0-9_-]+$ ]]
native="$repository/.lake/native-browser-prefix"
sdk="$repository/.lake/native-browser-sdk"
userspace="$repository/.lake/native-browser-sdk-usr"
alternatives="$repository/.lake/native-browser-sdk-alternatives"
[[ -f "$sdk/upstream/emscripten/emcc" && -f "$userspace/bin/cmake" ]]
mkdir -p "$work"
if [[ ! -d "$work/lean4/.git" ]]; then git clone --shared "$repository/.lake/native-browser-lean4" "$work/lean4"; fi
[[ $(git -C "$work/lean4" rev-parse HEAD) == 797c613eb9b6d4ec95db23e3e00af9ac6657f24b ]]
if git -C "$work/lean4" apply --check "$repository/web/tools/lean-wasm/lean-4.24-browser.patch"; then
 git -C "$work/lean4" apply "$repository/web/tools/lean-wasm/lean-4.24-browser.patch"
else
 git -C "$work/lean4" apply --reverse --check "$repository/web/tools/lean-wasm/lean-4.24-browser.patch"
fi
if [[ ! -d "$work/gmp/.git" ]]; then git clone --depth 1 --branch v6.2.1 https://github.com/alisw/GMP.git "$work/gmp"; fi
[[ $(git -C "$work/gmp" rev-parse HEAD) == 2bbd52703e5af82509773264bfbd20ff8464804f ]]
docker build --secret id=system_ca,src=/etc/ssl/certs/ca-certificates.crt -f "$repository/tests/directruntime-20261104/native-browser/Wasm.Dockerfile" -t "$image" "$repository/tests/directruntime-20261104/native-browser"
# Owned adapters change job count and cache location only; producer inputs stay read-only.
python3 - <<'GMP'
from pathlib import Path
p=Path("web/tools/lean-wasm/build-gmp.sh")
s=p.read_text()
assert s.count("make -j2 MAKEINFO=true")==1
activation="source /emsdk/emsdk_env.sh >/dev/null 2>&1"
assert s.count(activation)==1
s=s.replace("make -j2 MAKEINFO=true", "make -j1 MAKEINFO=true").replace(activation,activation+"\nexport EM_FROZEN_CACHE=0 EM_CACHE=/work/toolchain-cache")
Path("tests/directruntime-20261104/native-browser/gmp-serial.sh").write_text(s)
p=Path("web/tools/lean-wasm/build-compact-runtime.sh");s=p.read_text()
assert s.count(activation)==1
Path("tests/directruntime-20261104/native-browser/compact-runtime-cache.sh").write_text(s.replace(activation,activation+"\nexport EM_FROZEN_CACHE=0 EM_CACHE=/work/toolchain-cache"))
GMP
common=(--rm --memory=12g --memory-swap=12g --cpus=1 --user=1000:1000
 -e LEAN_NUM_THREADS=1 -e EMCC_CORES=1 -e BINARYEN_CORES=1 -e LAKE_CACHE_DIR=
 -e EM_FROZEN_CACHE=0 -e EM_CACHE=/work/toolchain-cache
 -e GIT_CONFIG_GLOBAL=/work/native-browser.gitconfig
 -v "$repository:$repository" -v "$work:/work"
 -v "$native:/native:ro" -v /workspace/.setup:/workspace/.setup:ro
 -v "$sdk:/emsdk:ro" -v "$userspace:/usr:ro" -v "$alternatives:/etc/alternatives:ro" -v /opt:/opt:ro
 -v /sys/fs/cgroup:/task-outer-cgroup:ro -v /etc/ssl/certs/ca-certificates.crt:/run/system-ca.pem:ro -w "$repository")
docker run "${common[@]}" --name "native-browser-wasm-$attempt" -e "NATIVE_BROWSER_WASM_ATTEMPT=$attempt" -e "NATIVE_LEAN_PREFIX=$native" -e "LEAN_BROWSER_WORK=$work" -e LEAN_WASM_SOURCE=/work/lean4 ubuntu:24.04 bash tests/directruntime-20261104/native-browser/wasm-inside.sh
