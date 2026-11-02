#!/usr/bin/env bash
set -euo pipefail
source /emsdk/emsdk_env.sh >/dev/null 2>&1
export EMCC_CORES=2 BINARYEN_CORES=2 LEAN_NUM_THREADS=1
if [[ -f /run/system-ca.pem ]]; then
  export GIT_SSL_CAINFO=/run/system-ca.pem SSL_CERT_FILE=/run/system-ca.pem REQUESTS_CA_BUNDLE=/run/system-ca.pem
fi
git config --global --add safe.directory /work/lean4
/native/bin/lean --version
cmake -S /work/lean4 -B /work/build64 -G 'Unix Makefiles' \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_TOOLCHAIN_FILE=/emsdk/upstream/emscripten/cmake/Modules/Platform/Emscripten.cmake \
  '-DCMAKE_C_FLAGS=-sMEMORY64=2 -mtail-call' '-DCMAKE_CXX_FLAGS=-sMEMORY64=2 -mtail-call' \
  -DSTAGE1_PREV_STAGE=/native -DSTAGE1_PREV_STAGE_CMAKE_EXECUTABLE_SUFFIX:STRING= -DUSE_MIMALLOC=OFF -DUSE_LAKE=OFF \
  -DCADICAL:FILEPATH= -DINSTALL_CADICAL=OFF -DUSE_GMP=ON -DGMP_INSTALL_PREFIX=/work/gmp-wasm64 \
  -DMMAP=OFF -DMULTI_THREAD=OFF '-DLEAN_EXTRA_CXX_FLAGS=-sMEMORY64=2' \
  '-DLEANC_OPTS=-sMEMORY64=2 -mtail-call' '-DLEAN_EXTRA_MAKE_OPTS=-j1' \
  -DBROWSER_RUNNER_FILTER=/work/internalize-runner.py -DBROWSER_FRONTEND_C=/work/BrowserFrontend.c -DBROWSER_BRIDGE_CPP=/browser/bridge.cpp \
  '-DLEAN_EXTRA_LINKER_FLAGS=-O0 -sASSERTIONS=0 -Wl,--lto-O0,--threads=2,--fatal-warnings -sMEMORY64=2 -sSTACK_SIZE=134217728 -sINITIAL_MEMORY=268435456 -sMAXIMUM_MEMORY=4294967296 -sMODULARIZE=0 -sDECLARE_ASM_MODULE_EXPORTS=0 -sENVIRONMENT=worker,node -sFORCE_FILESYSTEM=1 -sEXPORTED_FUNCTIONS=_main,_malloc,_free,_browser_init,_browser_check -sEXPORTED_RUNTIME_METHODS=FS,ccall,cwrap,UTF8ToString,stringToNewUTF8'
cmake --build /work/build64 --target stage1 --parallel 4
python3 /work/optimize-runtime.py /work/build64/stage1/bin/lean.js
