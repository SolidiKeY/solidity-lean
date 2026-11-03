#!/usr/bin/env bash
# Build the allocator/IO/arithmetic runtime only. No Lean kernel, elaborator,
# interpreter or serialized standard-library environment is built or shipped.
set -euo pipefail
source /emsdk/emsdk_env.sh >/dev/null 2>&1
export EMCC_CORES=1 BINARYEN_CORES=1 LEAN_NUM_THREADS=1
if [[ -f /run/system-ca.pem ]]; then
  export GIT_SSL_CAINFO=/run/system-ca.pem SSL_CERT_FILE=/run/system-ca.pem REQUESTS_CA_BUNDLE=/run/system-ca.pem
fi
git config --global --add safe.directory /work/lean4
cmake -S /work/lean4/src -B /work/build64/stage1 -G 'Unix Makefiles' \
  -DSTAGE=1 -DPREV_STAGE=/native -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX:STRING= \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_TOOLCHAIN_FILE=/emsdk/upstream/emscripten/cmake/Modules/Platform/Emscripten.cmake \
  '-DCMAKE_C_FLAGS=-sMEMORY64=2 -mtail-call' '-DCMAKE_CXX_FLAGS=-sMEMORY64=2 -mtail-call' \
  -DUSE_MIMALLOC=OFF -DUSE_LAKE=OFF -DCADICAL:FILEPATH= -DINSTALL_CADICAL=OFF \
  -DUSE_GMP=ON -DGMP_INSTALL_PREFIX=/work/gmp-wasm64 -DMMAP=OFF -DMULTI_THREAD=OFF
cmake --build /work/build64/stage1 --target leanrt --parallel 1
mkdir -p /work/build64/stage1/lib/temp
cp -asn /work/lean4/stage0/stdlib/. /work/build64/stage1/lib/temp/
