// Differential check against the unchanged recursive branch of pinned Lean.
// Compile with the patched Lean source/include directories and native lib path.
#include <cassert>
#include <iostream>
#include <random>
#include <sstream>
#include <stdexcept>
#include "kernel/replace_fn.h"
#include "kernel/init_module.h"
#include "util/init_module.h"
#include "runtime/stackinfo.h"
#define replace original_replace
#define replace_rec_fn original_replace_rec_fn
#define replace_fn original_replace_fn
#define lean_replace_expr original_lean_replace_expr
#include "kernel/replace_fn.cpp"
#undef lean_replace_expr
#undef replace_fn
#undef replace_rec_fn
#undef replace
#define LEAN_EMSCRIPTEN 1
#define replace browser_replace
#define replace_rec_fn browser_replace_rec_fn
#define replace_fn browser_replace_fn
#define lean_replace_expr browser_lean_replace_expr
#include "kernel/replace_fn.cpp"
#undef lean_replace_expr
#undef replace_fn
#undef replace_rec_fn
#undef replace
extern "C" lean_object * initialize_Init(uint8_t,lean_object*);
extern "C" lean_object * initialize_Std(uint8_t,lean_object*);
extern "C" lean_object * initialize_Lean(uint8_t,lean_object*);
using namespace lean;
static std::mt19937 random_source(42424);
static expr generate(unsigned depth) {
    if (!depth) {
        switch (random_source()%6) {
        case 0:return mk_bvar(random_source()%5);
        case 1:return mk_const(name("constant"));
        case 2:return mk_fvar(name("free"));
        case 3:return mk_mvar(name("meta"));
        case 4:return mk_lit(literal(static_cast<unsigned>(random_source()%8)));
        default:return mk_sort(mk_level_zero());
        }
    }
    expr a=generate(depth-1);
    switch(random_source()%9) {
    case 0:return mk_app(a,generate(depth-1));
    case 1:return mk_app(a,a);
    case 2:return mk_lambda(name("lambda"),a,generate(depth-1),static_cast<binder_info>(random_source()%5));
    case 3:return mk_pi(name("forall"),a,generate(depth-1),static_cast<binder_info>(random_source()%5));
    case 4:return mk_let(name("let"),a,generate(depth-1),generate(depth-1),random_source()%2);
    case 5:return mk_mdata(set_nat(kvmap(),name("metadata"),7),a);
    case 6:return mk_proj(name("Structure"),random_source()%3,a);
    case 7:return mk_app(a,mk_lambda(name("scope"),mk_sort(mk_level_zero()),a));
    default:return a;
    }
}
// Include every original payload pointer. Rebuilders must preserve these exact
// names, levels, metadata, literal values and binder/Let fields, not only ==.
static std::string structure(expr const & root) {
    std::ostringstream out;std::vector<expr const*> todo{&root};
    while(!todo.empty()) {
        expr const & e=*todo.back();todo.pop_back();out<<static_cast<int>(e.kind())<<':';
        switch(e.kind()) {
        case expr_kind::BVar:out<<bvar_idx(e).raw();break;
        case expr_kind::App:todo.push_back(&app_arg(e));todo.push_back(&app_fn(e));break;
        case expr_kind::Pi:case expr_kind::Lambda:
            out<<binding_name(e).raw()<<':'<<static_cast<unsigned>(binding_info(e));todo.push_back(&binding_body(e));todo.push_back(&binding_domain(e));break;
        case expr_kind::Let:
            out<<let_name(e).raw()<<':'<<let_nondep(e);todo.push_back(&let_body(e));todo.push_back(&let_value(e));todo.push_back(&let_type(e));break;
        case expr_kind::MData:out<<mdata_data(e).raw();todo.push_back(&mdata_expr(e));break;
        case expr_kind::Proj:out<<proj_sname(e).raw()<<':'<<proj_idx(e).raw();todo.push_back(&proj_expr(e));break;
        default:out<<e.raw();break;
        }
        out<<';';
    }
    return out.str();
}
using trace=std::vector<std::pair<lean_object*,unsigned>>;
static unsigned ffi_count;static trace ffi_trace;static expr const * ffi_alias;static unsigned ffi_mode;
static lean_object * ffi_callback(lean_object * raw) {
    expr e(raw);ffi_trace.emplace_back(raw,0);++ffi_count;
    optional<expr> result;
    if(ffi_mode==1&&e.kind()==expr_kind::BVar)result=some_expr(mk_bvar(ffi_count));
    if(ffi_mode==2&&ffi_count%7==0)result=some_expr(*ffi_alias);
    if(ffi_mode==3&&ffi_count==9)throw std::runtime_error("callback failure");
    if(!result)return lean_box(0);
    lean_object * option=lean_alloc_ctor(1,1,0);lean_inc(result->raw());lean_ctor_set(option,0,result->raw());return option;
}
int main() {
    save_stack_info();initialize_util_module();
    for(auto initialize:{initialize_Init,initialize_Std,initialize_Lean}){auto result=initialize(1,lean_io_mk_world());assert(lean_io_result_is_ok(result));lean_dec(result);}
    initialize_kernel_module();lean_io_mark_end_initialization();
    for(unsigned sample=0;sample<250;++sample) {
        expr root=generate(3+sample%3);
        for(unsigned mode=0;mode<5;++mode)for(bool cache:{false,true}) {
            trace events;unsigned count=0;
            auto callback=[&](expr const & e,unsigned offset)->optional<expr>{
                events.emplace_back(e.raw(),offset);++count;
                if(mode==1&&e.kind()==expr_kind::BVar)return some_expr(mk_bvar(offset+count));
                if(mode==2&&count%7==0)return some_expr(root);
                if(mode==3&&e.kind()==expr_kind::App)return some_expr(mk_bvar(offset+3));
                if(mode==4&&count==9)throw std::runtime_error("callback failure");
                return none_expr();
            };
            std::string expected,actual;bool old_error=false,new_error=false;
            try{expr result=original_replace(root,callback,cache);expected=structure(result);if(mode==0)assert(is_eqp(result,root));}catch(std::runtime_error const&){old_error=true;}
            trace old_events=events;events.clear();count=0;
            try{expr result=browser_replace(root,callback,cache);actual=structure(result);if(mode==0)assert(is_eqp(result,root));}catch(std::runtime_error const&){new_error=true;}
            assert(old_error==new_error&&expected==actual&&old_events==events);
        }
        for(ffi_mode=0;ffi_mode<4;++ffi_mode) {
            ffi_alias=&root;ffi_count=0;ffi_trace.clear();std::string expected,actual;bool old_error=false,new_error=false;
            auto closure=lean_alloc_closure(reinterpret_cast<void*>(ffi_callback),1,0);
            try{expr result(original_lean_replace_expr(closure,root.raw()));expected=structure(result);if(ffi_mode==0)assert(is_eqp(result,root));}catch(std::runtime_error const&){old_error=true;}
            trace old_events=ffi_trace;ffi_trace.clear();ffi_count=0;
            try{expr result(browser_lean_replace_expr(closure,root.raw()));actual=structure(result);if(ffi_mode==0)assert(is_eqp(result,root));}catch(std::runtime_error const&){new_error=true;}
            lean_dec(closure);assert(old_error==new_error&&expected==actual&&old_events==ffi_trace);
        }
    }
    expr deep=mk_bvar(0);for(unsigned i=0;i<50000;++i)deep=mk_app(deep,mk_bvar(0));
    auto unchanged=[](expr const&,unsigned){return none_expr();};
    assert(is_eqp(deep,browser_replace(deep,unchanged,true)));
    auto rewrite=[](expr const & e,unsigned n){return e.kind()==expr_kind::BVar?some_expr(mk_bvar(n+1)):none_expr();};
    expr result=browser_replace(deep,rewrite,true);
    assert(!is_eqp(result,deep));
    expr const * cursor=&result;
    for(unsigned i=0;i<50000;++i){assert(cursor->kind()==expr_kind::App&&is_bvar(app_arg(*cursor),1));cursor=&app_fn(*cursor);}
    assert(is_bvar(*cursor,1));
    expr scoped=mk_bvar(0);for(unsigned i=0;i<30000;++i)scoped=mk_lambda(name("deep"),mk_bvar(0),scoped);
    expr scoped_result=browser_replace(scoped,rewrite,true);cursor=&scoped_result;
    for(unsigned i=0;i<30000;++i){assert(cursor->kind()==expr_kind::Lambda&&is_bvar(binding_domain(*cursor),i+1));cursor=&binding_body(*cursor);}
    assert(is_bvar(*cursor,30001));
    std::cout<<"PASS 3,500 mixed/DAG differential cases, 50,000-deep applications and 30,000-deep binder offsets\n";
}
