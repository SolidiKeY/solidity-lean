#!/usr/bin/env python3
"""Build the import-free verifier using generated Lean C and Emscripten.
Usage: build-direct-runtime.py NATIVE_LEAN_PREFIX WASM_STAGE OUTPUT
Set EMCC when emcc is not on PATH. Run under the repository memory guard.
"""
import hashlib, importlib.util, json, os, pathlib, re, shutil, subprocess, sys
prefix, stage, output = map(lambda x:pathlib.Path(x).resolve(),sys.argv[1:])
output.mkdir(parents=True,exist_ok=True)
emcc=os.environ.get('EMCC','emcc')
root=pathlib.Path(__file__).resolve().parent.parent
commit=subprocess.check_output([str(prefix/'bin/lean'),'--githash'],text=True).strip()
if commit!='797c613eb9b6d4ec95db23e3e00af9ac6657f24b':raise ValueError('The direct verifier requires the pinned Lean runtime')
wasm_source=pathlib.Path(os.environ.get('LEAN_WASM_SOURCE',str(stage.parent.parent/'lean4')))
stage_commit=subprocess.check_output(['git','-C',str(wasm_source),'rev-parse','HEAD'],text=True).strip()
if stage_commit!=commit:raise ValueError('Wasm runtime source commit differs from the native compiler')
compiler=pathlib.Path(emcc).resolve()
if not compiler.is_file():
    import shutil
    compiler=pathlib.Path(shutil.which(emcc) or emcc).resolve()
clang=pathlib.Path(os.environ.get('EMCC_CLANG',str(compiler.parent.parent/'bin/clang')))
compiler_identity={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [compiler,compiler.with_suffix('.py'),clang]}
compiler_version=subprocess.check_output([emcc,'--version'],text=True).strip()
headers=hashlib.sha256()
for header in sorted((prefix/'include/lean').rglob('*.h')):
    headers.update(str(header.relative_to(prefix/'include')).encode());headers.update(header.read_bytes())
build_identity=hashlib.sha256(json.dumps({'compiler':compiler_identity,'version':compiler_version,'headers':headers.hexdigest(),'lean':commit},sort_keys=True).encode()).digest()

subprocess.run([str(prefix/'bin/lake'),'build','Solidity.Tools.DirectRuntime'],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)
setup=json.loads((root/'.lake/build/ir/Solidity/Tools/DirectRuntime.setup.json').read_text())
source_files=[]
for name in sorted({n for n in setup['importArts'] if n.startswith('Solidity.')}|{'Solidity.Tools.DirectRuntime'}):
    source_files.append({'module':name,'sourceSha256':hashlib.sha256((root/pathlib.Path(name.replace('.','/')+'.lean')).read_bytes()).hexdigest(),
      'cSha256':hashlib.sha256((root/'.lake/build/ir'/pathlib.Path(name.replace('.','/')+'.c')).read_bytes()).hexdigest()})
toolchain=(root/'lean-toolchain').read_text().strip()
full=os.environ.get('DIRECT_RUNTIME_FULL')=='1'
include=output/'include/lean'
include.mkdir(parents=True,exist_ok=True)
config=(prefix/'include/lean/config.h').read_text().replace('#define LEAN_MIMALLOC','/* wasm runtime uses the Lean allocator */')
(include/'config.h').write_text(config)
flags=['-I'+str(output/'include'),'-O2','-sMEMORY64=2','-mtail-call','-ffunction-sections','-fdata-sections','-DLEAN_EXPORTING','-I'+str(prefix/'include')]
if full:
    names=sorted({n for n in setup['importArts'] if n.startswith('Solidity.')}|{'Solidity.Tools.DirectRuntime'})
    inputs=[]
    for name in names:
        source=root/'.lake/build/ir'/pathlib.Path(name.replace('.','/')+'.c')
        raw=source.read_bytes();inputs.append((name,raw.decode(),source,hashlib.sha256(raw).hexdigest()))
    closure={'full':True}
    flags.append('-DSOLIDITY_DIRECT_FULL')
else:
    spec=importlib.util.spec_from_file_location('direct_closure',root/'scripts/direct-runtime-closure.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    undefined=subprocess.check_output([str(clang.parent/'llvm-nm'),'--undefined-only','--format=posix',str(stage/'lib/lean/libleanrt.a')],text=True)
    native_roots=set(re.findall(r'^(\w+) U ',undefined,re.M))
    inputs,closure=helper.extract(root,stage,native_roots=native_roots)
    print('Pure generated-C closure: '+json.dumps(closure),flush=True)
objects=[];sources=[]
for i,(name,text,source,expected) in enumerate(inputs):
    raw=text.encode();digest=hashlib.sha256(source.read_bytes()).hexdigest()
    if digest!=expected:raise ValueError('Generated source changed during extraction: '+name)
    key=hashlib.sha256(raw+config.encode()+json.dumps(flags).encode()+build_identity).hexdigest()
    obj=output/(key+'.o')
    if not obj.exists():
        snapshot=output/(key+'.c');snapshot.write_bytes(raw)
        temporary=output/(key+'.tmp.o')
        subprocess.run([emcc,*flags,'-c',str(snapshot),'-o',str(temporary)],check=True)
        temporary.replace(obj);snapshot.unlink()
    objects.append(str(obj))
    entry={'module':name,'cSha256':digest,'compiledCSha256':hashlib.sha256(raw).hexdigest()}
    if name.startswith('Solidity.'):
        entry['sourceSha256']=hashlib.sha256((root/pathlib.Path(name.replace('.','/')+'.lean')).read_bytes()).hexdigest()
    sources.append(entry)
    print(f'{i+1}/{len(inputs)} {name}',flush=True)
if not full:
    initializers=['initialize_'+n.replace('.','_') for n,_,_,_ in inputs]
    init='#include <lean/lean.h>\n'+''.join('extern lean_object* '+n+'(uint8_t,lean_object*);\n' for n in initializers)
    init+='lean_object* compact_initialize(void) { lean_object* res;\n'
    for n in initializers:
        init+='res='+n+'(1,lean_io_mk_world()); if(lean_io_result_is_error(res))return res; lean_dec(res);\n'
    init+='return lean_io_result_mk_ok(lean_box(0));}\n'
    source=output/'initialize.c';source.write_text(init)
    objects.append(str(source))
for name,_,source,expected in inputs:
    if hashlib.sha256(source.read_bytes()).hexdigest()!=expected:raise ValueError('Generated source changed during compilation: '+name)
lib=stage/'lib/lean'
libraries=[lib/n for n in (['libInit.a','libStd.a','libLean.a','libleancpp.a','libleanrt.a','libleanmanifest.a'] if full else ['libleanrt.a'])]
gmp=stage.parent.parent/'gmp-wasm64/lib/libgmp.a'
libraries.append(stage/'libuv/src/libuv/libuv.a')
subprocess.run([emcc,*flags,str(root/'web/browser/direct-bridge.c'),*objects,
    '-Wl,--start-group',*map(str,libraries),str(gmp),'-Wl,--end-group',
    '--no-entry','-fwasm-exceptions','-sMODULARIZE=1','-sEXPORT_NAME=createDirectVerifier','-sENVIRONMENT=worker,node',
    '-sALLOW_MEMORY_GROWTH=1','-sINITIAL_MEMORY=67108864','-sMAXIMUM_MEMORY=4294967296',
    '-sSTACK_SIZE=16777216','-sASSERTIONS=0',
    '-sEXPORTED_FUNCTIONS=_direct_init,_direct_check,_malloc,_free',
    '-sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString',
    '-Wl,--lto-O0,--threads=1','-o',str(output/'direct.js')],check=True)
for entry in source_files:
    for suffix,key in [('.lean','sourceSha256'),('.c','cSha256')]:
        file=(root if suffix=='.lean' else root/'.lake/build/ir')/pathlib.Path(entry['module'].replace('.','/')+suffix)
        if hashlib.sha256(file.read_bytes()).hexdigest()!=entry[key]:raise ValueError('Backend changed during build: '+entry['module'])
runtime_libraries={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [*libraries,gmp]}
manifest={'toolchain':toolchain,'sourceFiles':source_files,'bridgeSha256':hashlib.sha256((root/'web/browser/direct-bridge.c').read_bytes()).hexdigest(),'closureScriptSha256':hashlib.sha256((root/'scripts/direct-runtime-closure.py').read_bytes()).hexdigest(),'runtimeLibraries':runtime_libraries,'optimization':'-O2','version':1,'leanCommit':commit,'stageSourceCommit':stage_commit,'compiler':compiler_identity,'compilerVersion':compiler_version,'leanHeadersSha256':headers.hexdigest(),'modules':sources,'closure':closure,
 'javascript':hashlib.sha256((output/'direct.js').read_bytes()).hexdigest(),
 'wasm':hashlib.sha256((output/'direct.wasm').read_bytes()).hexdigest(),
 'wasmBytes':(output/'direct.wasm').stat().st_size}
(output/'build.json').write_text(json.dumps(manifest,indent=2)+'\n')
licenses=output/'licenses';licenses.mkdir(exist_ok=True)
for name in ['LICENSE','LICENSES']:shutil.copyfile(prefix/name,licenses/('Lean-'+name+'.txt'))
for name in ['COPYING','COPYING.LESSERv3','COPYINGv2','COPYINGv3']:
    file=stage.parent.parent/'gmp'/name
    if file.is_file():shutil.copyfile(file,licenses/('GMP-'+name+'.txt'))
for name in ['LICENSE','LICENSE-extra','LICENSE-docs']:
    file=stage/'libuv/src/libuv'/name
    if file.is_file():shutil.copyfile(file,licenses/('libuv-'+name+'.txt'))
emscripten=compiler.parent
for name in ['LICENSE','AUTHORS']:
    if (emscripten/name).is_file():shutil.copyfile(emscripten/name,licenses/('Emscripten-'+name+'.txt'))
print(json.dumps({k:v for k,v in manifest.items() if k!='modules'}),flush=True)
