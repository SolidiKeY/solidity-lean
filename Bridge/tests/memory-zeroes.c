/* Exact memset_zero body from EVMYulLean 047f63070309f436b66c61e276ab3b6d1169265a EvmYul/FFI/ffi.c.
   Licensed under Apache-2.0; see ../vendor/EvmYul/LICENSE.
   Observation fixture only; not a kernel proof of the FFI contract. */
#include "lean/lean.h"
#include <stdint.h>
#include <string.h>

extern lean_obj_arg memset_zero(size_t n) {
  lean_object* res = lean_alloc_sarray(1, n, n);
  uint8_t* it = lean_sarray_cptr(res);
  memset(it, 0, n);
  return res;
}
