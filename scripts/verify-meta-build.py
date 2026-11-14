#!/usr/bin/env python3
"""Compile the complete extended frontend closure, with observed C path probes."""
import hashlib,json,os,pathlib,platform,re,subprocess,sys
root=pathlib.Path.cwd().resolve()
prefix=pathlib.Path(sys.argv[1]).resolve()
out=pathlib.Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
commit='797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
if subprocess.check_output([str(prefix/'bin/lean'),'--githash'],text=True).strip()!=commit:
 raise ValueError('extended native toolchain mismatch')
run=lambda *args:subprocess.run(args,cwd=root,check=True,env={**os.environ,'LEAN_NUM_THREADS':'1'})
def digest_file(path):
 h=hashlib.sha256()
 with pathlib.Path(path).open('rb') as stream:
  for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
for name in ['LEAN_CC','LEAN_SYSROOT','CPATH','C_INCLUDE_PATH','CPLUS_INCLUDE_PATH','LIBRARY_PATH','COMPILER_PATH','LD_PRELOAD','LD_LIBRARY_PATH']:
 if os.environ.get(name):raise ValueError('unpinned native toolchain override: '+name)
source_paths=lambda:sorted((root/'Solidity').rglob('*.lean'))+[root/p for p in ['lean-toolchain','lakefile.toml','scripts/verify-meta-build.py']]
source_before={str(p):digest_file(p) for p in source_paths()}
sdk_paths=[prefix/'bin'/name for name in ['lean','lake','leanc','clang','ld.lld','llvm-ar']]
sdk_paths+=sorted((prefix/'include').rglob('*.h'))
sdk_paths+=[p for p in (prefix/'lib').rglob('*') if p.is_file() and (p.suffix in ['.a','.so','.dylib'] or '.so.' in p.name)]
sdk_before={str(p.resolve()):digest_file(p) for p in sdk_paths}
sdk_key=hashlib.sha256(json.dumps(sdk_before,sort_keys=True).encode()).hexdigest()
run(str(prefix/'bin/lake'),'build','Solidity.Tools.FastMode.Meta')
setup=json.loads((root/'.lake/build/ir/Solidity/Tools/FastMode/Meta.setup.json').read_text())
modules=sorted({m for m in setup['importArts'] if m.startswith('Solidity.')}|{'Solidity.Tools.FastMode.Meta'})
probes={
 'l_Solidity_Tools_FastMode_elabCheckExtended':'command',
 'l_Solidity_Recursion_autoGoal':'rec_auto',
 'l_Solidity_RecursionCallback_autoGoalC':'rec_auto_c',
 'l_Solidity_CallbackWalk_run':'sol_prove',
 'l_Solidity_Recursion_closeLeaf':'closing',
}
sha=lambda b:hashlib.sha256(b).hexdigest()
# Capture every source and actual imported artifact before compiling any C.
frozen={}
for module in modules:
 stem=module.replace('.','/')
 paths=[root/(stem+'.lean'),root/('.lake/build/ir/'+stem+'.c')]
 paths += [root/('.lake/build/lib/lean/'+stem+ext) for ext in ('.olean','.olean.private','.olean.server','.ir')
           if (root/('.lake/build/lib/lean/'+stem+ext)).is_file()]
 for path in paths:frozen[str(path)]=path.read_bytes()
for paths in setup['importArts'].values():
 for artifact in paths:
  path=pathlib.Path(artifact).resolve();frozen[str(path)]=path.read_bytes()
root_artifact=subprocess.check_output([str(prefix/'bin/lake'),'--quiet','query',
 'Solidity.Tools.FastMode.Meta:olean'],cwd=root,text=True).strip()
if not root_artifact.endswith('.olean') or not pathlib.Path(root_artifact).is_file():
 raise ValueError('unexpected root artifact query')
path=pathlib.Path(root_artifact).resolve();frozen[str(path)]=path.read_bytes()
for relative in ['lean-toolchain' ,'lakefile.toml','scripts/verify-meta-build.py']:
 path=root/relative;frozen[str(path)]=path.read_bytes()
objects=[];seen=set();compiled=[]
for module in modules:
 source=root/('.lake/build/ir/'+module.replace('.','/')+'.c')
 raw=frozen[str(source)];text=raw.decode();labels=[]
 for symbol,label in probes.items():
  pattern=r'(?m)^LEAN_EXPORT [^\n;]*\b'+re.escape(symbol)+r'\([^;\n]*\) \{\n'
  def instrument(match):
   return match[0]+'static unsigned char fast_meta_seen; if (!fast_meta_seen) { fast_meta_seen=1; const char* nonce=getenv("VERIFY_META_NATIVE_NONCE"); if(nonce) {fputs("FAST_META_C ",stdout);fputs(nonce,stdout);fputs(" '+label+chr(92)+'n",stdout);} }'+chr(10)
  text,count=re.subn(pattern,instrument,text)
  if count:
   if count!=1 or symbol in seen:raise ValueError('ambiguous native C probe: '+symbol)
   seen.add(symbol);labels.append(label)
 if labels:text='extern void* stdout; extern int fputs(const char*, void*); extern char* getenv(const char*);'+chr(10)+text
 captured=text.encode();key=sha(captured+sdk_key.encode()+b'-O0-DLEAN_EXPORTING')
 obj=out/(key+'.o')
 if not obj.exists():
  snapshot=out/(key+'.c');snapshot.write_bytes(captured)
  temporary=out/(key+'.tmp.o')
  run(str(prefix/'bin/leanc'),'-O0','-DLEAN_EXPORTING','-c',str(snapshot),'-o',str(temporary))
  temporary.replace(obj)
 objects.append(str(obj));compiled.append({'module':module,'sourceC':sha(raw),'compiledC':sha(captured),'probes':labels})
 print('compiled native module '+module,flush=True)
if seen!=set(probes):raise ValueError('required C probe definitions missing: '+str(set(probes)-seen))
plugin_name='libSolidity_Tools_FastMode_Meta.so'
temporary=out/('tmp-'+plugin_name)
run(str(prefix/'bin/leanc'),'-shared','-o',str(temporary),*objects)
if {str(p):digest_file(p) for p in source_paths()}!=source_before:
 raise ValueError('sources changed during native compilation')
if {p:digest_file(p) for p in sdk_before}!=sdk_before:
 raise ValueError('native SDK changed during compilation')
for path,raw in frozen.items():
 if pathlib.Path(path).read_bytes()!=raw:raise ValueError('native input changed: '+path)
digest=sha(temporary.read_bytes());plugin=out/digest/plugin_name
plugin.parent.mkdir(exist_ok=True)
if plugin.exists():
 if sha(plugin.read_bytes())!=digest:raise ValueError('corrupt native content-addressed output')
 temporary.unlink()
else:temporary.replace(plugin)
manifest={'version':1,'root':'Solidity.Tools.FastMode.Meta','leanCommit':commit,
 'sdk':str(prefix),'sdkFiles':sdk_before,'sourceBefore':source_before,'platform':sys.platform,'arch':{'x86_64':'x64','AMD64':'x64','aarch64':'arm64'}.get(platform.machine(),platform.machine()),'plugin':str(plugin),'pluginSha256':digest,
 'modules':compiled,'files':{path:sha(raw) for path,raw in frozen.items()},'probes':list(probes.values())}
new=out/'build.json.tmp';new.write_text(json.dumps(manifest,indent=2)+'\n');new.replace(out/'build.json')
