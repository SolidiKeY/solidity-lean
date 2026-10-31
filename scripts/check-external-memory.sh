#!/usr/bin/env bash
# Optional native evidence, separate from kernel-checked conditional refinement.
# Caller must hold the checkout writer lock and enforce repository resource bounds.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$repo_root/Bridge"
# The function body is verbatim from the already-pinned EVMYulLean commit;
# no hash/crypto library or network fetch is needed for memory observations.
mkdir -p .lake/build/memory-observe
sha256sum --check tests/memory-zeroes.SHA256
# Generate the actual interpreter ABI wrapper, rather than reimplementing it.
lake env lean -j1 --tstack=131072 -c .lake/build/memory-observe/ffi-generated.c vendor/EvmYul/FFI/ffi.lean
python3 - .lake/build/memory-observe/ffi-generated.c .lake/build/memory-observe/memory-abi.c <<'PYABI'
from pathlib import Path
import sys
src = Path(sys.argv[1]).read_text()
start = src.index('LEAN_EXPORT lean_object* l_ffi_ByteArray_zeroes___boxed(lean_object* x_1) {')
brace = src.index('{', start)
depth = 1
end = brace + 1
while depth:
    depth += (src[end] == '{') - (src[end] == '}')
    end += 1
Path(sys.argv[2]).write_text('#include "lean/lean.h"\nlean_object* memset_zero(size_t);\n' + src[start:end] + '\n')
PYABI
"${CC:-cc}" -shared -fPIC -I"$(lean --print-prefix)/include" tests/memory-zeroes.c .lake/build/memory-observe/memory-abi.c -o .lake/build/memory-observe/libmemory-zeroes.so
lake build SolidityBridge.ExternalEvm.MemoryRefinement SolidityBridge.ExternalEvm.MemoryComposition
exec lake env lean -j1 --tstack=131072 --load-dynlib=.lake/build/memory-observe/libmemory-zeroes.so --run tests/MemoryObserve.lean
