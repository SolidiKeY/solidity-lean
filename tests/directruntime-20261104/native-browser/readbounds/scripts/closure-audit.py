"""External exhaustive selected-C/object inventory; not semantic preservation."""
import argparse,hashlib,importlib.util,json,pathlib,re,subprocess,types
if not __debug__:raise RuntimeError("closure validation requires Python assertions enabled")
arguments=argparse.ArgumentParser(description=__doc__)
arguments.add_argument('--baseline-evidence-dir',type=pathlib.Path,required=True)
options=arguments.parse_args()
baseline_path=pathlib.Path(__file__).resolve().parents[1]/'baseline-inputs.py'
spec=importlib.util.spec_from_file_location('closure_baseline',baseline_path)
baseline_module=importlib.util.module_from_spec(spec);spec.loader.exec_module(baseline_module)
baseline=baseline_module.load(options.baseline_evidence_dir)
root=pathlib.Path.cwd();out=pathlib.Path('/workspace/scratch/browser-chain/readbounds-6513/closure');assert not out.exists();out.mkdir()
native=root/'.lake/native-browser-readbounds-6513/native';wasm=root/'.lake/native-browser-readbounds-6513/direct';prefix=root/'.lake/native-browser-prefix'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(name,d):
 with (out/name).open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
n=json.loads((native/'build.json').read_text());w=json.loads((wasm/'build.json').read_text());assert sha(native/'direct-check')==n['executable'];assert sha(wasm/'direct.wasm')==w['wasm'];bridge=sha(root/'web/browser/direct-bridge.c');assert bridge==n['bridgeSha256']==w['bridgeSha256']
for e in n['sourceFiles']:
 stem=e['module'].replace('.','/');assert sha(root/(stem+'.lean'))==e['sourceSha256'];assert sha(root/'.lake/build/ir'/(stem+'.c'))==e['cSha256']
for path,digest in n['buildInputs'].items():assert sha(pathlib.Path(path))==digest,path
source=root/'scripts/direct-runtime-closure.py';assert sha(source)==n['closureScriptSha256']==w['closureScriptSha256'];helper=types.ModuleType('closure');helper.__file__=str(source);exec(compile(source.read_bytes(),str(source),'exec'),helper.__dict__)
u=subprocess.check_output(['nm','--undefined-only','--format=posix',str(prefix/'lib/lean/libleanrt.a')],text=True);inputs,stats=helper.extract(root,native/'runtime',native_roots=set(re.findall(r'^(\w+) U ',u,re.M)));assert stats==n['closure']==w['closure']
flags=['-O2','-ffunction-sections','-fdata-sections','-I'+str(prefix/'include')];identity=json.dumps(n['buildInputs'],sort_keys=True);records=[];texts={}
wm={e['module']:e for e in w['modules']};differences=[]
for module,text,path,original in inputs:
 assert sha(path)==original;digest=hashlib.sha256(text.encode()).hexdigest();key=hashlib.sha256((text+str(flags)+identity).encode()).hexdigest();obj=native/(key+'.o');assert obj.is_file(),module
 if wm.get(module,{}).get('compiledCSha256')!=digest:differences.append(module)
 records.append({'module':module,'originalCSha256':original,'compiledCSha256':digest,'object':str(obj),'objectSha256':sha(obj),'functions':sorted(m[1] for m in helper.FUNC.finditer(text))});texts[module]=text
assert set(wm)==set(texts)
save('selected-C-objects.json',records)
symbols=subprocess.check_output(['nm','-C','--defined-only',str(native/'direct-check')],text=True);(out/'native-symbols.txt').write_text(symbols)
blocked=re.compile(r"\b(?:lean_initialize|lean_import_modules|l_Lean_importModules|l_Lean_(?:Elab|Meta|Environment|Kernel)_\w*|initialize_Lean_(?:Elab|Meta|Environment|Kernel)\w*)\b|lean::(?:environment|type_checker|module_mgr)\b")
coarse=[line for line in symbols.splitlines() if blocked.search(line)];save('coarse-origin-scan.json',{'binarySha256':n['executable'],'flags':coarse,'passed':not coarse,'boundary':'Conservative origin-name scan, retained separately from exact-body classification.'})
old=baseline['native-stub-classification.json']['data'];assert old['passed'];oldCoarse=baseline['native-audit.json']['data'];assert baseline['native-audit.json']['sha256']==old['coarseReceiptSha256'];assert oldCoarse['binarySha256']==old['binarySha256']
oldIdent=baseline['native-input-identities.json']['data']
for path,digest in oldIdent['headers'].items():assert sha(prefix/path)==digest
machine_calls={'lean_dec_ref_cold','lean_nat_big_lt','lean_string_utf8_get','lean_string_utf8_next','lean_nat_big_eq','lean_notify_assert','lean_inc_heartbeat','lean_internal_panic_out_of_memory','mi_malloc_small'}
def machine_transfers(assembly, symbol):
 """Classify x86 calls and every jump, rejecting unclassified destinations."""
 calls=set();branches=set();invalid=False
 for instruction in re.finditer(r'\b(callq?|j[a-z]+|loop[a-z]*)\s+([^\n]+)', assembly):
  mnemonic,operand=instruction.groups()
  direct=re.fullmatch(r'[0-9a-f]+ <([^>]+)>\s*',operand)
  if direct is None:
   invalid=True
   continue
  target=direct.group(1)
  if mnemonic.startswith('call'):
   calls.add(target)
  elif target.split('+',1)[0] != symbol:
   branches.add(target)
 return calls,branches,invalid

classified=[];failures=[];modules={r['module']:r for r in records};actualFlags={line.split()[-1] for line in coarse};expectedFlags={'initialize_'+r['module'].replace('.','_') for r in old['records']}
if actualFlags!=expectedFlags:failures.append('origin symbol set changed')
frontend={m for m in texts if m.startswith(('Lean.Meta','Lean.Elab','Lean.Kernel','Lean.Environment'))}
if frontend!={r['module'] for r in old['records']}:failures.append('frontend-origin module set changed')
for record in old['records']:
 module=record['module'];assert modules[module]['compiledCSha256']==record['compiledCSha256'],module;details=[]
 for f in record['functions']:
  symbol=f['symbol'];asm=subprocess.check_output(['objdump','-d','--disassemble='+symbol,str(native/'direct-check')],text=True);calls,tails,invalid=machine_transfers(asm,symbol)
  if '<'+symbol+'>:' not in asm:failures.append('missing disassembly label: '+symbol)
  if not (calls|tails)<=machine_calls:failures.append('unreviewed machine transfer: '+symbol)
  if invalid:failures.append('unclassified or indirect transfer: '+symbol)
  details.append({'symbol':symbol,'baselineCBodySha256':f['cBodySha256'],'machineCallees':sorted(calls),'disassembly':asm})
 classified.append({'module':module,'exactCompiledCMatchesReviewedBaseline':True,'functions':details})
undefined=subprocess.check_output(['nm','--undefined-only','--format=posix',str(native/'direct-check')],text=True);leanUndefined=[s for s in undefined.splitlines() if s.split() and s.split()[0].startswith(('l_','_init_l_','lean_','initialize_'))]
if leanUndefined:failures.append('unresolved Lean imports')
dynamic=subprocess.check_output(['readelf','-d',str(native/'direct-check')],text=True);(out/'native-dynamic.txt').write_text(dynamic)
if re.search(r'NEEDED.*(?:liblean|libLean)',dynamic):failures.append('dynamic Lean library')
node='/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin/node';js="const fs=require('fs');const m=new WebAssembly.Module(fs.readFileSync(process.argv[1]));console.log(JSON.stringify({imports:WebAssembly.Module.imports(m),exports:WebAssembly.Module.exports(m)}));";interface=json.loads(subprocess.check_output([node,'-e',js,str(wasm/'direct.wasm')],text=True));save('wasm-interface.json',interface)
save('origin-classification.json',{'binarySha256':n['executable'],'baselineClassificationSha256':baseline['native-stub-classification.json']['sha256'],'coarseReceiptSha256':sha(out/'coarse-origin-scan.json'),'records':classified,'unresolvedLeanImports':leanUndefined,'failures':failures,'passed':not failures,'boundary':'Exact compiled C bodies of all frontend-origin modules equal independently reviewed baseline; current machine callees checked. No namespace exemption or general purity/semantic theorem.'})
report={'nativeSha256':n['executable'],'wasmSha256':w['wasm'],'bridgeSha256':bridge,'closureScriptSha256':sha(source),'closure':stats,'selectedModulesInventoried':len(records),'compiledCParityDifferences':differences,'originClassificationPassed':not failures,'staticSelectedCParityPassed':not differences,'wasmInterface':interface,'newOrChangedWorkerTheorems':[],'boundary':'Exhaustive inventory of selected extracted C modules/objects and static imports/exports, plus exact-body classification and request-specific runtime traces elsewhere. Not exhaustive source grammar, intrinsic/source preservation or universal native correctness.'};save('summary.json',report);print(json.dumps({k:report[k] for k in ['selectedModulesInventoried','compiledCParityDifferences','originClassificationPassed','staticSelectedCParityPassed']}));assert not failures and not differences
