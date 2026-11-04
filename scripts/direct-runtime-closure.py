"""Reachability for Lean-generated C with explicit, closed-data initialization.

Retain every function/closure reference reachable from the exported pure API,
including dependencies of all referenced closed values. Fail on unfamiliar
initialization rather than loading null or skipping a required effect.
"""
import re
import hashlib
from bisect import bisect_right
from pathlib import Path
def file_sha256(path):
    """Hash incrementally so runtime archives do not become resident copies."""
    digest=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024), b''):
            digest.update(block)
    return digest.hexdigest()

def snapshot_files(paths):
    """Pin the exact selected file set as well as its contents."""
    return {str(path):file_sha256(path) for path in sorted(set(map(Path,paths)))}

def verify_snapshot(expected, paths):
    actual=snapshot_files(paths)
    if actual!=expected:
        changed=sorted(key for key in expected.keys()|actual.keys()
                       if expected.get(key)!=actual.get(key))
        raise ValueError('Build inputs changed: '+', '.join(changed))

IDENT=re.compile(r'\b[A-Za-z_]\w*\b')
FUNC=re.compile(r'^(?:(?:LEAN_EXPORT|static)\s+)?[A-Za-z_][\w *]*?\s+(\w+)\([^;\n]*\) \{',re.M)
GLOBAL=re.compile(r'^(?:(?:LEAN_EXPORT|static)\s+)?(?:lean_object\s*\*|uint\d+_t|int\d+_t|size_t|double|float)\s*(\w+)\s*;',re.M)

BRACES=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[{}]',re.S)
def end_brace(text,start):
    depth=0
    for m in BRACES.finditer(text,text.index('{',start)):
        if m[0]=='{':depth+=1
        elif m[0]=='}':
            depth-=1
            if depth==0:return m.end()
    raise ValueError('Unterminated generated C function')

def collect(root,stage,module):
    seen={};order=[]
    def visit(name):
        if name in seen:return
        if name.startswith('Solidity.'):
            path=root/'.lake/build/ir'/Path(name.replace('.','/')+'.c')
        else:path=stage/'lib/temp'/Path(name.replace('.','/')+'.c')
        text=path.read_text();m=re.search(r'^// Imports: ?(.*)$',text,re.M)
        if not m:raise ValueError('Missing generated C import header: '+str(path))
        functions={}
        for match in FUNC.finditer(text):
            end=end_brace(text,match.start())
            functions[match[1]]=(match.start(),end,text[match.start():end])
        init='initialize_'+name.replace('.','_')
        if init not in functions:raise ValueError('Missing module initializer: '+name)
        intervals=sorted((a,b) for a,b,_ in functions.values())
        starts=[a for a,b in intervals]
        globals=set()
        for declaration in GLOBAL.finditer(text):
            pos=bisect_right(starts,declaration.start())-1
            if pos<0 or declaration.start()>=intervals[pos][1]:globals.add(declaration[1])
        initializer=functions[init][2]
        assignments={}
        marked=set(re.findall(r'^lean_mark_persistent\((\w+)\);$',initializer,re.M))
        for assignment in re.finditer(r'^(\w+) = (_init_\w+)\(\);$',initializer,re.M):
            g=assignment[1]
            if g in globals and assignment[2]=='_init_'+g:
                mark='lean_mark_persistent('+g+');'
                assignments[g]=(assignment[2],assignment[0]+'\n'+(mark+'\n' if g in marked else ''))
        seen[name]={'path':path,'text':text,'functions':functions,'globals':globals,'assignments':assignments,'init':init}
        for dep in m[1].split():visit(dep)
        order.append(name)
    visit(module)
    return seen,order

def extract(root,stage,module='Solidity.Tools.DirectRuntime',native_roots=()):
    native_roots=set(native_roots)
    modules,order=collect(root,stage,module)
    definitions={};global_defs={}
    for name,m in modules.items():
        for f,(_,_,body) in m['functions'].items():
            if f.startswith('initialize_'):continue
            if f in definitions:raise ValueError('Duplicate generated function: '+f)
            definitions[f]=(name,body)
        for g in m['globals']:
            if g in global_defs:raise ValueError('Duplicate generated global: '+g)
            global_defs[g]=name
    functions=set();globals=set();pending=['solidity_direct_check','lean_io_eprintln','lean_list_to_array','lean_array_to_list_impl','lean_io_error_to_string','lean_mk_io_user_error','lean_stream_of_handle']
    initializer_names={m['init'] for m in modules.values()}
    # Archive undefined references include platform/libc symbols, which the
    # linker resolves. Generated Lean callbacks must instead exist in the
    # collected graph: silently filtering one would hide an incomplete closure.
    missing_native=sorted(s for s in native_roots
                          if s.startswith(('l_','_init_l_'))
                          and s not in definitions and s not in global_defs)
    if missing_native:
        raise ValueError('Unresolved generated native roots: '+', '.join(missing_native))
    retained_native=sorted(s for s in native_roots if s in definitions or s in global_defs)
    pending.extend(retained_native)
    while pending:
        symbol=pending.pop()
        if symbol in initializer_names:raise ValueError('Initializer called from pure API: '+symbol)
        if symbol in definitions:
            if symbol in functions:continue
            functions.add(symbol);pending.extend(IDENT.findall(definitions[symbol][1]))
        elif symbol in global_defs:
            if symbol in globals:continue
            globals.add(symbol);m=modules[global_defs[symbol]]
            if symbol not in m['assignments']:
                raise ValueError('Reachable value requires unsupported initialization: '+symbol+' in '+str(m['path']))
            pending.append(m['assignments'][symbol][0])
        elif symbol.startswith(('l_','_init_l_')):
            raise ValueError('Unresolved generated Lean symbol: '+symbol)
    outputs=[]
    for name in order:
        m=modules[name];needed=[g for g in globals if global_defs[g]==name]
        if not needed and not any(f in functions for f in m['functions']):continue
        # Keep original assignment order: a closed value can use one initialized
        # earlier in this same module. Import order is preserved by collect().
        original=m['functions'][m['init']][2]
        needed.sort(key=lambda g:original.index(m['assignments'][g][1].splitlines()[0]))
        initializer='LEAN_EXPORT lean_object* '+m['init']+'(uint8_t builtin, lean_object* w) {\n'
        initializer+=''.join(m['assignments'][g][1] for g in needed)
        initializer+='return lean_io_result_mk_ok(lean_box(0));\n}'
        text=m['text']
        for f,(start,end,body) in sorted(m['functions'].items(),key=lambda kv:kv[1][0],reverse=True):
            replacement=initializer if f==m['init'] else body if f in functions else ''
            text=text[:start]+replacement+text[end:]
        outputs.append((name,text,m['path'],hashlib.sha256(m['text'].encode()).hexdigest()))
    return outputs,{'modules':len(outputs),'functions':len(functions),'closedValues':len(globals),'sourceModules':len(modules),'nativeRoots':retained_native}
