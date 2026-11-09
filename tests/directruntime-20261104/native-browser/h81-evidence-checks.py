"""Bind fresh controls/packages and preserve failed performance/functional gates."""
import base64,hashlib,json,math,pathlib,re,statistics,subprocess
root=pathlib.Path.cwd();base=pathlib.Path('/workspace/scratch/browser-chain');out=base/'h81-evidence';assert not out.exists();out.mkdir()
def load(p):return json.loads(pathlib.Path(p).read_text())
def sha(p):
 h=hashlib.sha256()
 with pathlib.Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(n,d):
 with (out/n).open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
mem=load(base/'h81-memory/control-inventory-with-guard.json');producer=load(root/'tests/directruntime-20261104/memory-references/manifest.json');assert mem['producerManifestSha256']==sha(root/'tests/directruntime-20261104/memory-references/manifest.json')
key=lambda r:r['id']+'.'+r['modality']+'.'+('ir' if r['viaIR'] else 'non-ir');cases={key(r):r for r in producer['cases']};assert len(cases)==84
assert {r['caseKey'] for r in mem['requests']}==set(cases)
for row in mem['requests']:
 assert row['sourceHash']==cases[row['caseKey']]['sourceSha256']==sha(root/row['original']);assert row['fixtureSha256']==sha(row['fixture']);assert row['compilerHeader']['compilerSha256']==producer['compilerSha256']
parity=[];errors=[];concrete=0;required=0
for a,b in zip(mem['native'],mem['browser']):
 assert a['caseKey']==b['caseKey'];assert a['reply']['results']==b['reply']['results'];row=cases[a['caseKey']];status=a['reply']['results'][0]['status'];assert row['requiredProven']==(status=='proved'),(a['caseKey'],status)
 if row['requiredProven']:required+=1
 if row['modelHalt'] in ['success','panic','revert']:
  expected='proved' if row['modelHalt']=='success' else 'refuted' if row['modelHalt']=='panic' or row['modality']=='diamond' else 'proved';assert status==expected,(a['caseKey'],status,expected);concrete+=1
 parity.append({'caseKey':a['caseKey'],'status':status,'sourceSha256':row['sourceSha256']})
assert len(parity)==84 and mem['identityNonVacuityComplete'] and not mem['requiredControlFailures']
save('memory-parity.json',{'casesPerBackend':84,'exactResultObjectParity':True,'requiredProvenCasesSatisfiedPerBackend':required,'concreteModelHaltExpectationsSatisfiedPerBackend':concrete,'identityDiamondAndPairedControlsPassed':True,'results':parity,'pending':mem['supportGaps'],'counterexamplesIndependentlyReplayed':False,'boundary':'Fresh compiled-checker observations and exact source/compiler/request identity. Model controls and source preservation are separate; pending is not refuted.'})
n=load(root/'.lake/native-browser-h81/native/build.json');w=load(root/'.lake/native-browser-h81/direct/build.json');assert n['executable']==sha(root/'.lake/native-browser-h81/native/direct-check');assert w['wasm']==sha(root/'.lake/native-browser-h81/direct/direct.wasm');assert w['javascript']==sha(root/'.lake/native-browser-h81/direct/direct.js')
html=root/'web/single-file/index.html';assets={name:base64.b64decode(data) for name,data in re.findall(r'<script type="application/octet-stream" data-asset="([^"]+)" data-mime="[^"]+">([^<]*)</script>',html.read_text())};wasms=[(name,data) for name,data in assets.items() if name.endswith('direct.wasm')];assert len(wasms)==1 and hashlib.sha256(wasms[0][1]).hexdigest()==w['wasm'];package=load(root/'web/single-file/build.json');assert package['compiledOnly'] and package['kernelBuild'] is None and package['runtimeSha256']==w['wasm']
for row in mem['browser']:assert row['boot']['build']==w['wasm']
browser=load(base/'h81-browser-benchmark/browser.json');assert browser['runtime']['build']==w['wasm'] and browser['assetBuild']==package['build']
save('artifact-binding.json',{'nativeSha256':n['executable'],'wasmSha256':w['wasm'],'javascriptSha256':w['javascript'],'htmlSha256':sha(html),'package':package,'embeddedAssets':list(assets),'runtimeBuildObserved':browser['runtime']['build'],'kernelAssetNames':[x for x in assets if re.search(r'\.(olean|ilean)|kernel-worker|/lean/',x)],'boundary':'Boot metadata, actual embedded WASM bytes, native executable and repeated worker identities agree. Standard WASM env/WASI imports are not Lean Environment loads.'})
assert not any(re.search(r'\.(olean|ilean)|kernel-worker|/lean/',x) for x in assets)
def metric(d,start):
 assert d['passed'] and len(d['trials'])==249;names={r['name'] for r in d['trials']};assert len(names)==83
 for name in names:assert sorted(r['round'] for r in d['trials'] if r['name']==name)==[0,1,2]
 v=sorted(statistics.median(r['wallMs'] for r in d['trials'] if r['name']==name) for name in names);return {'medianMs':statistics.median(v),'p95Ms':v[math.ceil(.95*len(v))-1],'startupMs':d[start]}
old=load(root/'docs/benchmarks/directruntime-2026-11-04/hardening/comparison-summary.json');current={'nativeAst':metric(load(base/'h81-native/checks/native.json'),'startupMs'),'browser':metric(browser,'startupMs')};perf={}
for mode,cur in current.items():
 before=old[mode]['before'];ratios={k:cur[k]/before[k] for k in cur};perf[mode]={'before':before,'current':cur,'ratios':ratios,'stopMetrics':[k for k,v in ratios.items() if v>1.10]}
save('performance-stops.json',{'comparisons':perf,'gate':'STOP retained; no unchanged candidate rerun or threshold relaxation','boundary':'Three rounds83functions each; median/p95 of per-function medians. Startup is one fresh page/process observation, not machine-cold. H68 payload and new runtime/UI changes confounded.'})
a=load(root/'docs/benchmarks/directruntime-2026-11-04/before/inputs/inputs.json');b=load(base/'h81-native/checks/inputs/inputs.json')
def strip(x):
 if isinstance(x,dict):return {k:strip(v) for k,v in x.items() if k not in ['typeIdentifier','tryCall']}
 if isinstance(x,list):return [strip(v) for v in x]
 return x
assert all(x['name']==y['name'] and x['sourceHash']==y['sourceHash'] for x,y in zip(a['trials'],b['trials']));save('payload-comparison.json',{'cases':83,'sameSourceHashes':True,'equalAfterRemovingTypeIdentifierAndTryCall':sum(strip(x['request'])==strip(y['request']) for x,y in zip(a['trials'],b['trials'])),'boundary':'Saved-data comparison only; does not establish slowdown cause.'})
intake=pathlib.Path('/workspace/h82-handoffs/h82b-20261106T180909Z');count=0
for line in (intake/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);p=intake/name;assert p.resolve().is_relative_to(intake.resolve()) and sha(p)==expected;count+=1
scope=load(intake/'assignments/browser/scope.json');assert scope['write_namespace']=='live';member=load(intake/'assignments/browser/solidity-directruntime-20261104__native-browser.json');subprocess.run(['git','merge-base','--is-ancestor',member['merge_first'],'HEAD'],check=True)
save('intake.json',{'filesVerified':count,'manifestSha256':sha(intake/'manifest.json'),'scopeSha256':sha(intake/'assignments/browser/scope.json'),'memberMergeFirstAncestor':member['merge_first'],'boundary':'Browser chain has no additional members in dispatch. Metadata receipt does not provide missing external archives/caches or transfer other-chain scope.'})
assert not subprocess.check_output(['git','diff','--name-only','HEAD','--','*.lean'],text=True).strip();save('worker-axiom-inventory.json',{'newOrChangedWorkerTheorems':[],'trackedLeanChanges':[],'registration':'not applicable: no new Lean source module','boundary':'Existing producer12kernel control checks are separate; no new D theorem/axiom/premise/budget change.'})
print(json.dumps({'memoryCases':84,'concreteExpectations':concrete,'requiredProven':required,'performanceStops':{k:v['stopMetrics'] for k,v in perf.items()},'intakeFiles':count}))
