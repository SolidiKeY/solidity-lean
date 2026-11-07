"""Guard ordinary runtime closure against the published optional kernel-candidate helpers.
A complete hash-bound executable/symbol inventory,not source/ABI preservation.
"""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path.cwd();out=Path('/workspace/scratch/browser-chain/address-postmerge');destination=out/'candidate-exclusion.json';assert not destination.exists();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inventoryPath=out/'closure/selected-C-objects.json';summaryPath=out/'closure/summary.json';inventory=json.loads(inventoryPath.read_text());summary=json.loads(summaryPath.read_text());native=root/'.lake/native-browser-address-postmerge/native';wasm=root/'.lake/native-browser-address-postmerge/direct';n=json.loads((native/'build.json').read_text());w=json.loads((wasm/'build.json').read_text());binary=native/'direct-check';assert sha(binary)==n['executable'];assert sha(wasm/'direct.wasm')==w['wasm'];assert summary['nativeSha256']==n['executable'] and summary['wasmSha256']==w['wasm'];assert summary['staticSelectedCParityPassed'] and summary['originClassificationPassed'] and not summary['compiledCParityDifferences'];assert summary['closure']==n['closure']==w['closure'];assert summary['selectedModulesInventoried']==len(inventory)==n['closure']['modules']>0
modules=[x['module'] for x in inventory];assert len(set(modules))==len(modules);wm={x['module']:x for x in w['modules']};assert set(modules)==set(wm)
for x in inventory:
 p=Path(x['object']);p.resolve().relative_to(native.resolve());assert sha(p)==x['objectSha256'];assert x['compiledCSha256']==wm[x['module']]['compiledCSha256']
for m in [n,w]:
 for e in m['sourceFiles']:assert sha(root/(e['module'].replace('.','/')+'.lean'))==e['sourceSha256']
pattern=re.compile(r'sourceValuesV1|SourceCounterexampleCandidateV1|sourceCounterexampleCandidateV1|refuteSourceCandidateV1');selected=[{'module':x['module'],'symbol':f} for x in inventory for f in x['functions'] if pattern.search(f)];symbols=subprocess.check_output(['nm','--defined-only',str(binary)],text=True);found=[line for line in symbols.splitlines() if pattern.search(line)];assert not selected and not found,(selected,found)
report={'passed':True,'newOptionalHelpersSelected':selected,'newOptionalHelperNativeSymbols':found,'nativeSha256':n['executable'],'wasmSha256':w['wasm'],'modulesInventoried':len(inventory),'inventorySha256':sha(inventoryPath),'companionSummarySha256':sha(summaryPath),'nativeManifestSha256':sha(native/'build.json'),'wasmManifestSha256':sha(wasm/'build.json'),'sourceBuildHead':'0eb39db1dba7f81e4d8d0b4756ab50b87d4dcd6d','actualHead':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'boundary':'AllselectedC/object/currentbinary manifests bound to passingWASM/nativecompanionclosure. Newoptionalhelper families absent;not universalpurity,sourcepreservation orwhole-goal acceptance.'}
with destination.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print('PASS complete hash-bound selectedC/nativebinary exclude optionalkernel-candidate helpers')
