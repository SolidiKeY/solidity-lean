#include <lean/lean.h>
#include <emscripten/emscripten.h>
#ifdef SOLIDITY_DIRECT_FULL
extern void lean_initialize(void);
#else
extern void lean_initialize_runtime_module(void);
extern lean_object* compact_initialize(void);
#endif
extern lean_object* initialize_Solidity_Tools_DirectRuntime(uint8_t, lean_object*);
extern lean_object* solidity_direct_check(lean_object*);
static lean_object* previous_result;
static int initialized;
EMSCRIPTEN_KEEPALIVE int direct_init(void) {
  if (initialized) return 0;
#ifdef SOLIDITY_DIRECT_FULL
  lean_initialize();
  lean_object* result = initialize_Solidity_Tools_DirectRuntime(1, lean_io_mk_world());
#else
  lean_initialize_runtime_module();
  lean_object* result = compact_initialize();
#endif
  if (!lean_io_result_is_ok(result)) {
    lean_io_result_show_error(result);lean_dec(result);return 2;
  }
  lean_dec(result);lean_io_mark_end_initialization();
  lean_init_task_manager_using(1);initialized=1;return 0;
}
EMSCRIPTEN_KEEPALIVE const char* direct_check(const char* input) {
  if (!initialized) return "{\"gap\":\"runtime not initialized\"}";
  if (previous_result) { lean_dec(previous_result); previous_result = NULL; }
  previous_result=solidity_direct_check(lean_mk_string(input));
  return lean_string_cstr(previous_result);
}
