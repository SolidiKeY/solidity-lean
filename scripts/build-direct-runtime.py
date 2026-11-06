#!/usr/bin/env python3
"""Build the import-free verifier using generated Lean C and Emscripten.
Usage: build-direct-runtime.py NATIVE_LEAN_PREFIX WASM_STAGE OUTPUT
Set EMCC when emcc is not on PATH and EM_CONFIG to its explicit SDK config.
Run under the repository memory guard.
"""
import hashlib, importlib.util, json, os, pathlib, re, shutil, subprocess, sys, tempfile
for override in ['LEAN_CC','LEAN_SYSROOT','CPATH','C_INCLUDE_PATH','CPLUS_INCLUDE_PATH','LIBRARY_PATH','COMPILER_PATH']:
    if os.environ.get(override):
        raise ValueError('Unpinned compiler override: '+override)
if os.environ.get('DIRECT_RUNTIME_FULL')=='1':
    raise ValueError('Full Lean runtime is not an ordinary verifier; use a separate optional certification pipeline')
for override in ['EMCC_CFLAGS','EM_COMPILER_WRAPPER','EM_LLVM_ROOT','EM_BINARYEN_ROOT']:
    if os.environ.get(override):raise ValueError('Unpinned compiler override: '+override)
if not os.environ.get('EM_CONFIG') or not pathlib.Path(os.environ['EM_CONFIG']).is_file():
    raise ValueError('Pinned WASM builds require an explicit EM_CONFIG file')
prefix, stage, output = map(lambda x:pathlib.Path(x).resolve(),sys.argv[1:])
output.mkdir(parents=True,exist_ok=True)
emcc=os.environ.get('EMCC','emcc')
root=pathlib.Path(__file__).resolve().parent.parent
closure_path=root/'scripts/direct-runtime-closure.py'
closure_bytes=closure_path.read_bytes()
spec=importlib.util.spec_from_file_location('direct_closure',closure_path)
helper=importlib.util.module_from_spec(spec)
exec(compile(closure_bytes,str(closure_path),'exec'),helper.__dict__)
bridge_path=root/'web/browser/direct-bridge.c'
bridge_bytes=bridge_path.read_bytes()
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
config_path=pathlib.Path(os.environ['EM_CONFIG']).resolve()
os.environ['EM_CONFIG']=str(config_path)
config_initial=hashlib.sha256(config_path.read_bytes()).hexdigest()
configured=json.loads(subprocess.check_output([sys.executable,'-E','-c',
    "import sys,json; sys.path.insert(0,sys.argv[1]); from tools import config,shared; "
    "print(json.dumps(dict(clang=shared.CLANG_CC,ar=shared.LLVM_AR,nm=shared.LLVM_NM,ld=shared.WASM_LD,"
    "binaryen=config.BINARYEN_ROOT,node=config.NODE_JS,wrapper=config.COMPILER_WRAPPER)))",
    str(compiler.parent)],text=True))
if pathlib.Path(configured['clang']).resolve()!=clang.resolve():raise ValueError('Configured clang differs from the pinned compiler')
if configured['wrapper']:raise ValueError('Configured compiler wrappers are not supported')
configured_tools=[pathlib.Path(configured[n]) for n in ['clang','ar','nm','ld']]
configured_tools+=sorted(p for p in (pathlib.Path(configured['binaryen'])/'bin').iterdir() if p.is_file())
node=configured['node']
configured_tools.append(pathlib.Path(node[0] if isinstance(node,list) else node))
compiler_identity={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [compiler,compiler.with_suffix('.py'),clang]}
emcc=str(compiler)
compiler_version=subprocess.check_output([sys.executable,'-E',str(compiler.with_suffix('.py')),'--version'],text=True).strip()
headers=hashlib.sha256()
for header in sorted((prefix/'include/lean').rglob('*.h')):
    headers.update(str(header.relative_to(prefix/'include')).encode());headers.update(header.read_bytes())
build_identity=hashlib.sha256(json.dumps({'compiler':compiler_identity,'version':compiler_version,'headers':headers.hexdigest(),'lean':commit},sort_keys=True).encode()).digest()

def provenance_paths():
    return [pathlib.Path(__file__).resolve(),closure_path,bridge_path,root/'lean-toolchain',root/'lakefile.toml',
            pathlib.Path(sys.executable),*map(pathlib.Path,compiler_identity),*configured_tools,prefix/'bin/lean',prefix/'bin/lake',
            *sorted(compiler.parent.rglob('*.py')),
            config_path,
            *sorted((prefix/'include').rglob('*.h')),
            *sorted((stage/'lib/lean').glob('*.a')),
            stage/'libuv/src/libuv/libuv.a',stage.parent.parent/'gmp-wasm64/lib/libgmp.a']
provenance=helper.snapshot_files(provenance_paths())
# Pinning the SDK's tool set should not keep unused tool binaries resident
# throughout compilation. This only advises clean pages; bytes are unchanged.
if hasattr(os,'posix_fadvise'):
    for tool in configured_tools:
        with tool.open('rb') as stream:
            os.posix_fadvise(stream.fileno(),0,0,os.POSIX_FADV_DONTNEED)

if provenance[str(config_path)]!=config_initial:raise ValueError('Emscripten config changed during discovery')
if any(provenance[p]!=digest for p,digest in compiler_identity.items()):raise ValueError('Compiler changed before snapshot')
headers_check=hashlib.sha256()
for header in sorted((prefix/'include/lean').rglob('*.h')):
    headers_check.update(str(header.relative_to(prefix/'include')).encode());headers_check.update(header.read_bytes())
if headers_check.digest()!=headers.digest():raise ValueError('Headers changed before snapshot')
if provenance[str(closure_path)]!=hashlib.sha256(closure_bytes).hexdigest():raise ValueError('Closure changed before snapshot')
if provenance[str(bridge_path)]!=hashlib.sha256(bridge_bytes).hexdigest():raise ValueError('Bridge changed before snapshot')
build_identity+=hashlib.sha256(json.dumps(provenance,sort_keys=True).encode()).digest()

subprocess.run([str(prefix/'bin/lake'),'build','Solidity.Tools.DirectRuntime'],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)
setup=json.loads((root/'.lake/build/ir/Solidity/Tools/DirectRuntime.setup.json').read_text())
source_files=[]
for name in sorted({n for n in setup['importArts'] if n.startswith('Solidity.')}|{'Solidity.Tools.DirectRuntime'}):
    source_files.append({'module':name,'sourceSha256':hashlib.sha256((root/pathlib.Path(name.replace('.','/')+'.lean')).read_bytes()).hexdigest(),
      'cSha256':hashlib.sha256((root/'.lake/build/ir'/pathlib.Path(name.replace('.','/')+'.c')).read_bytes()).hexdigest()})
toolchain=(root/'lean-toolchain').read_text().strip()
full=False
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
    undefined=subprocess.check_output([configured['nm'],'--undefined-only','--format=posix',str(stage/'lib/lean/libleanrt.a')],text=True)
    native_roots=set(re.findall(r'^(\w+) U ',undefined,re.M))
    # A separate serial process releases the large temporary parser graph and
    # its allocator arenas before compilation. Pass the captured helper bytes,
    # not a second read of mutable producer code.
    extraction=pathlib.Path(tempfile.mkdtemp(prefix='extract-',dir=output))
    captured=extraction/'closure.py';captured.write_bytes(closure_bytes)
    roots_file=extraction/'roots.json';roots_file.write_text(json.dumps(sorted(native_roots)))
    extracted=extraction/'inputs.json'
    worker='''import json,pathlib,sys,types
helper=types.ModuleType('closure')
p=pathlib.Path(sys.argv[1]);exec(compile(p.read_bytes(),str(p),'exec'),helper.__dict__)
inputs,closure=helper.extract(pathlib.Path(sys.argv[2]),pathlib.Path(sys.argv[3]),native_roots=json.loads(pathlib.Path(sys.argv[4]).read_text()))
pathlib.Path(sys.argv[5]).write_text(json.dumps(dict(inputs=inputs,closure=closure),default=str))
'''
    subprocess.run([sys.executable,'-E','-c',worker,str(captured),str(root),str(stage),str(roots_file),str(extracted)],check=True)
    payload=json.loads(extracted.read_text())
    inputs=[(name,text,pathlib.Path(source),expected) for name,text,source,expected in payload['inputs']]
    closure=payload['closure'];del payload
    shutil.rmtree(extraction)
    if hasattr(os,'posix_fadvise'):
        # Extraction has finished reading these immutable originals. Compilers
        # consume the captured/pruned buffers, not the original source files.
        for directory in [stage/'lib/temp',root/'.lake/build/ir']:
            for original in directory.rglob('*.c'):
                with original.open('rb') as stream:
                    os.posix_fadvise(stream.fileno(),0,0,os.POSIX_FADV_DONTNEED)
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
        subprocess.run([sys.executable,'-E',str(compiler.with_suffix('.py')),*flags,'-c',str(snapshot),'-o',str(temporary)],check=True)
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
link_output=pathlib.Path(tempfile.mkdtemp(prefix='link-',dir=output))
bridge_source=output/('bridge-'+hashlib.sha256(bridge_bytes).hexdigest()+'.c')
bridge_source.write_bytes(bridge_bytes)
subprocess.run([sys.executable,'-E',str(compiler.with_suffix('.py')),*flags,str(bridge_source),*objects,
    '-Wl,--start-group',*map(str,libraries),str(gmp),'-Wl,--end-group',
    '--no-entry','-fwasm-exceptions','-sMODULARIZE=1','-sEXPORT_NAME=createDirectVerifier','-sENVIRONMENT=worker,node',
    '-sALLOW_MEMORY_GROWTH=1','-sINITIAL_MEMORY=67108864','-sMAXIMUM_MEMORY=4294967296',
    '-sSTACK_SIZE=16777216','-sASSERTIONS=0',
    '-sEXPORTED_FUNCTIONS=_direct_init,_direct_check,_malloc,_free',
    '-sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString',
    '-Wl,--lto-O0,--threads=1','-o',str(link_output/'direct.js')],check=True)
for entry in source_files:
    for suffix,key in [('.lean','sourceSha256'),('.c','cSha256')]:
        file=(root if suffix=='.lean' else root/'.lake/build/ir')/pathlib.Path(entry['module'].replace('.','/')+suffix)
        if hashlib.sha256(file.read_bytes()).hexdigest()!=entry[key]:raise ValueError('Backend changed during build: '+entry['module'])
for name,_,source,expected in inputs:
    if helper.file_sha256(source)!=expected:raise ValueError('Generated source changed during link: '+name)
helper.verify_snapshot(provenance,provenance_paths())
runtime_libraries={str(p):provenance[str(p)] for p in [*libraries,gmp]}
manifest={'toolchain':toolchain,'sourceFiles':source_files,'bridgeSha256':hashlib.sha256(bridge_bytes).hexdigest(),'closureScriptSha256':hashlib.sha256(closure_bytes).hexdigest(),'buildInputs':provenance,'runtimeLibraries':runtime_libraries,'optimization':'-O2','version':1,'leanCommit':commit,'stageSourceCommit':stage_commit,'compiler':compiler_identity,'compilerVersion':compiler_version,'configuredTools':configured,'leanHeadersSha256':headers.hexdigest(),'modules':sources,'closure':closure,
 'javascript':hashlib.sha256((link_output/'direct.js').read_bytes()).hexdigest(),
 'wasm':hashlib.sha256((link_output/'direct.wasm').read_bytes()).hexdigest(),
 'wasmBytes':(link_output/'direct.wasm').stat().st_size}
for name in ['direct.wasm','direct.js']:
    (link_output/name).replace(output/name)
link_output.rmdir()
manifest_tmp=output/'build.json.tmp'
manifest_tmp.write_text(json.dumps(manifest,indent=2)+'\n')
manifest_tmp.replace(output/'build.json')
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
