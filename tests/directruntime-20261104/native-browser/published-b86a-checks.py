"""Validate observed admission/provenance; do not infer semantic acceptance."""
import gzip,hashlib,json,pathlib,re,subprocess
root=pathlib.Path.cwd();out=root/'docs/benchmarks/directruntime-2026-11-04/published-b86a'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
log=(out/'producer-signatures-admission.log').read_text()
entries=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log)
expected={'Solidity.Frontend.ExecutableAst.Shared.'+n for n in ['executableExpression','executableStatements','executableReader']}
assert len(entries)==3 and {n for n,_ in entries}==expected
assert 'sorryAx' not in log
for n,axioms in entries:assert {a.strip() for a in axioms.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'}
lineage=json.loads((out/'api-wrapper-lineage.json').read_text());assert hashlib.sha256(gzip.decompress((out/lineage['executedWrapperArchive']).read_bytes())).hexdigest()==lineage['executedWrapperSha256']
admission=json.loads((out/'composed-admission.json').read_text());control=json.loads((out/'C-controls/control-inventory-with-guard.json').read_text());assert len(admission['functions'])==13 and {r['name'] for r in admission['functions']}==set(control['names']);assert not admission['intrinsicProof'] and not admission['runtimeVerdict'];assert not control['semanticAcceptanceComplete'] and not control['identityNonVacuityComplete']
producer=json.loads((out/'producer-inventory.json').read_text());assert sha(root/(producer['module'].replace('.','/')+'.lean'))==producer['sourceSha256'];assert sha(root/'.lake/native-browser-b86a-admission.lean')==producer['admissionTestInputSha256']
aliases={'/emsdk/':str(root/'.lake/native-browser-sdk')+'/', '/work/':str(root/'.lake/native-browser-wasm')+'/', '/usr/':str(root/'.lake/native-browser-sdk-usr')+'/'};bindings={}
for mode,folder,binary,key in [('native','native','direct-check','executable'),('wasm','direct','direct.wasm','wasm')]:
 path=root/'.lake/native-browser-f77'/folder;m=json.loads((path/'build.json').read_text())
 for e in m['sourceFiles']:
  stem=e['module'].replace('.','/');assert sha(root/(stem+'.lean'))==e['sourceSha256'];assert sha(root/'.lake/build/ir'/(stem+'.c'))==e['cSha256']
 for file,digest in m['buildInputs'].items():
  mapped=file
  if mode=='wasm':
   for prefix,replacement in aliases.items():
    if file.startswith(prefix):mapped=replacement+file[len(prefix):];break
  assert sha(pathlib.Path(mapped))==digest,file
 assert sha(path/binary)==m[key];assert control['freshness'][mode]['binarySha256']==m[key]
 bindings[mode]={'binary':str(path/binary),'binarySha256':m[key],'manifestSha256':sha(path/'build.json'),'currentSourceAndCFilesVerified':len(m['sourceFiles']),'buildInputsVerified':len(m['buildInputs']),'freshBuildThisTurn':False}
unchanged=['Solidity/Tools/DirectRuntime.lean','Solidity/Calculus/ReadBounds.lean','Solidity/Calculus/QueryReadBounds.lean','web/browser/direct-bridge.c','tests/directruntime-20261104/control-tuples/Controls.sol']
for p in unchanged:assert subprocess.check_output(['git','show','f77cf60d3cea8f7f1db8db29cc027532b0cd3fce:'+p])==(root/p).read_bytes()
assert not subprocess.check_output(['git','diff','--name-only','b86ae4568cef6d6226f4d170360bbb089debe3fb','HEAD','--','*.lean'],text=True).strip()
report={'passed':True,'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'publishedBase':'b86ae4568cef6d6226f4d170360bbb089debe3fb','exactDefinitionAxiomTargetSet':sorted(expected),'workerLeanChanges':[],'bindings':bindings,'wasmBuildMountAliases':aliases,'unchangedSinceF77':unchanged,'functionAdmissionAccepted':sum(r['accepted'] for r in admission['functions']),'functionAdmissionRefused':sum(not r['accepted'] for r in admission['functions']),'rootStorageValidationOnly':True,'cachedVerdictsUsed':False,'newBenchmarkOrStackRetest':False,'boundary':'Observed inventory, not a complete expected-admission regression oracle. Reuses revalidated f77 binaries, not new builds. Published composition admission, intrinsic proof and runtime support remain separate.'}
with (out/'metadata-validation.json').open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print('PASS exact definition targets,13 admission observations and current source/C/build-input/binary pins')
