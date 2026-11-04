#!/usr/bin/env bash
set -euo pipefail
repository=$(pwd -P)
work="$repository/.lake/native-browser-wasm"
image=solidity-lean-native-browser-wasm:4.24
attempt=${NATIVE_BROWSER_WASM_ATTEMPT:-before-1}
[[ $attempt =~ ^[A-Za-z0-9_-]+$ ]]
native="$repository/.lake/native-browser-prefix"
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
# Only the make job count changes in this owned adapter; producer inputs stay read-only.
python3 - <<'GMP'
from pathlib import Path
p=Path("web/tools/lean-wasm/build-gmp.sh")
s=p.read_text()
assert s.count("make -j2 MAKEINFO=true")==1
Path("tests/directruntime-20261104/native-browser/gmp-serial.sh").write_text(s.replace("make -j2 MAKEINFO=true", "make -j1 MAKEINFO=true"))
GMP
common=(--rm --memory=12g --memory-swap=12g --cpus=1 --user=1000:1000
 -e LEAN_NUM_THREADS=1 -e EMCC_CORES=1 -e BINARYEN_CORES=1
 -e GIT_CONFIG_GLOBAL=/work/native-browser.gitconfig
 -v "$repository:$repository" -v "$work:/work"
 -v "$native:/native:ro" -v /workspace/.setup:/workspace/.setup:ro
 -v /sys/fs/cgroup:/task-outer-cgroup:ro -v /etc/ssl/certs/ca-certificates.crt:/run/system-ca.pem:ro -w "$repository")
for step in gmp compact direct; do
 case "$step" in
 gmp) command=(bash tests/directruntime-20261104/native-browser/gmp-serial.sh);;
 compact) command=(bash web/tools/lean-wasm/build-compact-runtime.sh);;
 direct) command=(bash web/tools/lean-wasm/build-direct.sh);;
 esac
 docker run "${common[@]}" --name "native-browser-wasm-$step" -e "NATIVE_LEAN_PREFIX=$native" -e "LEAN_BROWSER_WORK=$work" -e LEAN_WASM_SOURCE=/work/lean4 "$image" python3 tests/directruntime-20261104/native-browser/bounded-command.py "docs/benchmarks/directruntime-2026-11-04/before/wasm-$attempt-$step-gate.json" "${command[@]}"
done
