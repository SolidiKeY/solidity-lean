"""Bind fresh f77 builds, requests and package identities; report incomplete acceptance."""
import base64,hashlib,json,math,pathlib,re,statistics,subprocess
root=pathlib.Path.cwd();out=root/'docs/benchmarks/directruntime-2026-11-04/published-f77'
def load(p):return json.loads((root/p).read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def save(name,d):
 with (out/name).open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
def metric(d,start):
 assert d['passed'] and len(d['trials'])==249
 names={t['name'] for t in d['trials']};assert len(names)==83
 assert all(sorted(t['round'] for t in d['trials'] if t['name']==n)==[0,1,2] for n in names)
 v=sorted(statistics.median(t['wallMs'] for t in d['trials'] if t['name']==n) for n in names)
 return {'functions':83,'rounds':3,'requests':249,'medianMs':statistics.median(v),'p95Ms':v[math.ceil(.95*len(v))-1],'startupMs':d[start]}
manifest={};binaries={}
for mode,folder,name,key in [('native','native','direct-check','executable'),('wasm','direct','direct.wasm','wasm')]:
 path=root/'.lake/native-browser-f77'/folder;d=load(path/'build.json');manifest[mode]=d;binaries[mode]=sha(path/name);assert binaries[mode]==d[key]
 for e in d['sourceFiles']:
  assert sha(root/(e['module'].replace('.','/')+'.lean'))==e['sourceSha256']
 assert sha(root/'web/browser/direct-bridge.c')==d['bridgeSha256']
 assert sha(root/'scripts/direct-runtime-closure.py')==d['closureScriptSha256']
 save(mode+'-build-manifest.json',d)
html=root/'web/single-file/index.html';text=html.read_text();assets={name:base64.b64decode(data) for name,data in re.findall(r'<script type="application/octet-stream" data-asset="([^"]+)" data-mime="[^"]+">([^<]*)</script>',text)}
wasm=[(name,data) for name,data in assets.items() if name.endswith('direct.wasm')];assert len(wasm)==1
assert hashlib.sha256(wasm[0][1]).hexdigest()==binaries['wasm']
assert not any(re.search(r'\.(olean|ilean)|kernel-worker|/lean/',n) for n in assets)
browser=load(out/'browser.json');package=load('web/single-file/build.json')
assert browser['runtime']['build']==package['runtimeSha256']==binaries['wasm']
assert browser['assetBuild']==package['build'] and package['compiledOnly'] and package['kernelBuild'] is None
controls=load(out/'C-controls/control-inventory-with-guard.json');assert controls['inventoryCompleted'] and controls['positiveHarnessGuard']['passed']
for mode in ['native','wasm']:assert controls['freshness'][mode]['binarySha256']==binaries[mode]
assert all(r['boot']['build']==binaries['wasm'] for r in controls['browser'])
save('browser-binary-binding.json',{'passed':True,'runtimeBuild':browser['runtime']['build'],'wasmSha256':binaries['wasm'],'htmlSha256':sha(html),'package':package,'embeddedWasmName':wasm[0][0],'embeddedAssets':list(assets),'ordinaryEnvironmentAssets':[],'boundary':'Recorded benchmark runtime.build, embedded WASM bytes and separate worker boots agree with fresh WASM manifest. External observations, not a source-soundness proof.'})
old=load('docs/benchmarks/directruntime-2026-11-04/hardening/comparison-summary.json');baseline={'nativeAst':old['nativeAst']['before'],'browser':old['browser']['before']}
ext=load('docs/benchmarks/directruntime-2026-11-04/before/extension.json');baseline['nativeSourceLsp']=metric(ext,'initializationMs')
current={'nativeAst':metric(load(out/'native.json'),'startupMs'),'browser':metric(browser,'startupMs'),'nativeSourceLsp':metric(load(out/'extension.json'),'initializationMs')}
comparisons={}
for name,cur in current.items():
 ratios={k:cur[k]/baseline[name][k] for k in ['medianMs','p95Ms','startupMs']}
 comparisons[name]={'before':baseline[name],'freshF77':cur,'ratios':ratios,'overTenPercent':any(v>1.10 for v in ratios.values())}
save('performance-summary.json',{'comparisons':comparisons,'method':'Median and nearest-rank p95 of 83 per-function medians across three rounds. Startup is one process/page observation; not machine-cold. Native AST excludes Solidity compile; source LSP/browser include live compilation.','builds':{n:load(out/(n+'-build-gate.json')) for n in ['native','wasm']},'artifactBytes':{'native':(root/'.lake/native-browser-f77/native/direct-check').stat().st_size,'wasm':(root/'.lake/native-browser-f77/direct/direct.wasm').stat().st_size,'html':html.stat().st_size},'buildComparisonLimit':'Native f77 build includes PrintStmt-invalidated Lean jobs plus empty C/object/link output. Earlier cold-C run replayed warm Lean artifacts; whole build wall times are not matched. No full cold-before measurement exists.','postTranslatorIntegration':False})
changed=subprocess.check_output(['git','diff','--name-only','f77cf60d3cea8f7f1db8db29cc027532b0cd3fce','HEAD','--','*.lean'],text=True).splitlines();assert not changed
assert not subprocess.check_output(['git','diff','--name-only','HEAD','--','*.lean'],text=True).strip()
assert not [p for p in subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines() if p.endswith('.lean')]
save('axiom-inventory.json',{'publishedBase':'f77cf60d3cea8f7f1db8db29cc027532b0cd3fce','workerLeanChanges':changed,'newOrChangedWorkerTheorems':[],'printAxiomsCommands':[],'status':'not applicable: no new or changed worker Lean declarations','boundary':'Producer APIs retain their exact declarations/premises; no claim of producer source adequacy or completed runtime integration.'})
print(json.dumps(comparisons,indent=2))
