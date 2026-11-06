#!/usr/bin/env bash
set -euo pipefail
source /emsdk/emsdk_env.sh >/dev/null 2>&1
mkdir -p /work/gmp-build64
cd /work/gmp-build64
emconfigure ../gmp/configure --host=none --build=x86_64-pc-linux-gnu --disable-assembly --disable-shared --enable-static --prefix=/work/gmp-wasm64 CC='emcc -sMEMORY64=1' CFLAGS='-O2 -sMEMORY64=1 -flto -fwasm-exceptions' CC_FOR_BUILD=gcc
# Automake's default target generates BUILT_SOURCES (fib_table.h and the
# other limb tables) before compiling the library. The direct libgmp.la target
# skips those prerequisites in a fresh Git checkout.
# Only libgmp and its headers are packaged; the SDK does not need texinfo or
# a regenerated Info manual. Propagate the override through recursive make.
make -j2 MAKEINFO=true
mkdir -p /work/gmp-wasm64/lib /work/gmp-wasm64/include
cp .libs/libgmp.a /work/gmp-wasm64/lib/
cp gmp.h /work/gmp-wasm64/include/
cat > /work/layout.c <<'C'
#include <stdio.h>
#include <gmp.h>
#include <stdint.h>
_Static_assert(sizeof(void*)==8,"pointer width");
_Static_assert(sizeof(size_t)==8,"size_t width");
_Static_assert(sizeof(long)==8,"long width");
_Static_assert(sizeof(mp_limb_t)==8,"limb width");
_Static_assert(sizeof(__mpz_struct)==16,"mpz layout");
_Static_assert(GMP_NUMB_BITS==64,"numb bits");
_Static_assert(GMP_NAIL_BITS==0,"nail bits");
int main(void){mpz_t n;mpz_init(n);mpz_ui_pow_ui(n,2,256);gmp_printf("GMP64 layout OK; 2^256 = %Zd\n",n);mpz_clear(n);return 0;}
C
emcc -sMEMORY64=2 -fwasm-exceptions -O2 /work/layout.c /work/gmp-wasm64/lib/libgmp.a -I/work/gmp-wasm64/include -o /work/layout.js
node /work/layout.js
