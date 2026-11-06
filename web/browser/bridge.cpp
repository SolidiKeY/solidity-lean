#include <lean/lean.h>
#include <emscripten/emscripten.h>
#include <gmp.h>
#include "githash.h"
#include <cstdio>
#include <exception>
#include "library/elab_environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/replace_fn.h"

static_assert(sizeof(void*)==8 && sizeof(size_t)==8 && sizeof(long)==8,"Lean library word layout");
static_assert(sizeof(mp_limb_t)==8 && sizeof(__mpz_struct)==16 && GMP_NUMB_BITS==64 && GMP_NAIL_BITS==0,"Lean library integer layout");
extern "C" EMSCRIPTEN_KEEPALIVE const char* browser_identity() {
    return LEAN_VERSION_STRING "|" LEAN_GITHASH "|64|64";
}

extern "C" void lean_initialize();
extern "C" lean_object* initialize_web_browser_BrowserFrontend(uint8_t, lean_object*);
extern "C" lean_object* browser_lean_check(lean_object*, lean_object*, lean_object*);
extern "C" lean_object* lean_enable_initializer_execution(lean_object*);
extern "C" lean_object* lean_io_promise_new(lean_object*);
extern "C" lean_object* lean_io_promise_result_opt(lean_object*);
extern "C" lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
extern "C" lean_object* lean_mk_empty_environment(uint32_t, lean_object*);

static bool initialized=false;
static int consume_result(lean_object* result) {
    if (!lean_io_result_is_ok(result)) {
        lean_io_result_show_error(result);
        lean_dec(result);
        return 2;
    }
    lean_dec(result);
    return 0;
}

extern "C" EMSCRIPTEN_KEEPALIVE int browser_init() {
    if (initialized) return 0;
    lean_initialize();
    if (consume_result(initialize_web_browser_BrowserFrontend(1, lean_io_mk_world()))) return 2;
    lean_io_mark_end_initialization();
    lean_init_task_manager_using(1);
    initialized=true;
    return 0;
}

static lean_object* probe_promise_value(lean_object* option) {
    const size_t value=lean_is_scalar(option)?0:lean_unbox(lean_ctor_get(option,0));
    lean_dec(option);
    return lean_box(value);
}

static lean_object* probe_bind_task(lean_object* next, lean_object* previous) {
    lean_dec(previous);
    return next;
}

static lean_object* probe_new_promise() {
    lean_object* result=lean_io_promise_new(lean_io_mk_world());
    if (!lean_io_result_is_ok(result)) {consume_result(result);return nullptr;}
    lean_object* promise=lean_io_result_get_value(result);
    lean_inc(promise);lean_dec(result);
    return promise;
}

extern "C" EMSCRIPTEN_KEEPALIVE int browser_promise_probe() {
    lean_object* promise=probe_new_promise();
    if (!promise) return 2;
    lean_object* task=lean_io_promise_result_opt(promise);
    lean_object* mapped=lean_task_map_core(lean_alloc_closure((void*)probe_promise_value,1,0),task,0,false,false);
    if (consume_result(lean_io_promise_resolve(lean_box(42),promise,lean_io_mk_world()))) return 2;
    const int value=static_cast<int>(lean_unbox(lean_task_get(mapped)));
    lean_dec(promise);lean_dec(mapped);
    if (value!=42) return 2;

    lean_object* first=probe_new_promise();
    lean_object* second=probe_new_promise();
    if (!first||!second) return 2;
    lean_object* bind_fn=lean_alloc_closure((void*)probe_bind_task,2,1);
    lean_closure_set(bind_fn,0,lean_io_promise_result_opt(second));
    lean_object* bound=lean_task_bind_core(lean_io_promise_result_opt(first),bind_fn,0,false,false);
    if (consume_result(lean_io_promise_resolve(lean_box(1),first,lean_io_mk_world()))) return 2;
    if (lean_io_get_task_state_core(bound)==2) return 2;
    if (consume_result(lean_io_promise_resolve(lean_box(42),second,lean_io_mk_world()))) return 2;
    lean_object* option=lean_task_get(bound);
    const bool bind_ok=!lean_is_scalar(option)&&lean_unbox(lean_ctor_get(option,0))==42;
    lean_dec(first);lean_dec(second);lean_dec(bound);
    if (!bind_ok) return 2;

    lean_object* dropped=probe_new_promise();
    if (!dropped) return 2;
    lean_object* dropped_task=lean_io_promise_result_opt(dropped);
    lean_dec(dropped);
    const bool drop_ok=lean_is_scalar(lean_task_get(dropped_task))&&lean_io_get_task_state_core(dropped_task)==2;
    lean_dec(dropped_task);
    return drop_ok?0:2;
}

extern "C" EMSCRIPTEN_KEEPALIVE int browser_kernel_probe() {
    try {
        // Exercise the compiled browser traversal beyond the engine's machine
        // stack limit, including binder offsets, before allowing proof results.
        lean::expr deep=lean::mk_bvar(0);
        const lean::name binder("browserStackProbe");
        for (unsigned i=0;i<6000;++i) deep=lean::mk_lambda(binder,lean::mk_bvar(0),deep);
        lean::expr replaced=lean::replace(deep,[](const lean::expr & e,unsigned offset) {
            return lean::is_bvar(e)?lean::some_expr(lean::mk_bvar(offset+1)):lean::none_expr();
        });
        const lean::expr * cursor=&replaced;
        for (unsigned i=0;i<6000;++i) {
            if (cursor->kind()!=lean::expr_kind::Lambda||!lean::is_bvar(lean::binding_domain(*cursor),i+1)) return 2;
            cursor=&lean::binding_body(*cursor);
        }
        if (!lean::is_bvar(*cursor,6001)) return 2;
        lean_object* result=lean_mk_empty_environment(0,lean_io_mk_world());
        if (!lean_io_result_is_ok(result)) return consume_result(result);
        lean_object* raw=lean_io_result_get_value(result);
        lean_inc(raw);lean_dec(result);
        lean::elab_environment frontend(raw);
        lean::environment env=frontend.to_kernel_env();
        const lean::expr prop=lean::mk_sort(lean::mk_level_zero());
        const lean::expr type=lean::mk_sort(lean::mk_succ(lean::mk_level_zero()));
        const auto hints=lean::reducibility_hints::mk_opaque();
        env=env.add(lean::mk_definition(lean::name("browserKernelGood"),lean::names(),type,prop,hints),true);
        try {
            env.add(lean::mk_definition(lean::name("browserKernelBad"),lean::names(),prop,prop,hints),true);
        } catch (const lean::definition_type_mismatch_exception&) {
            return 0;
        }
        return 2;
    } catch (const std::exception& error) {
        std::fprintf(stderr,"Lean kernel startup test: %s\n",error.what());
        return 2;
    }
}

extern "C" EMSCRIPTEN_KEEPALIVE int browser_check(const char* source, const char* file_name) {
    try {
    if (browser_init()) return 2;
    if (consume_result(lean_enable_initializer_execution(lean_io_mk_world()))) return 2;
    lean_object* result=browser_lean_check(lean_mk_string(source),lean_mk_string(file_name),lean_io_mk_world());
    if (!lean_io_result_is_ok(result)) return consume_result(result);
    const int code=static_cast<int>(lean_unbox_uint32(lean_io_result_get_value(result)));
    lean_dec(result);
    return code;
    } catch (const std::exception& error) {
        std::fprintf(stderr,"Lean browser exception: %s\n",error.what());
        return 2;
    } catch (...) {
        std::fputs("Lean browser exception: unknown native exception\n",stderr);
        return 2;
    }
}
