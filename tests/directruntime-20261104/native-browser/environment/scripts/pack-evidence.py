from pathlib import Path
import hashlib,json,tarfile
root=Path.cwd();scratch=Path('/workspace/scratch/browser-chain/environment');private=root/'.lake/native-browser-environment';target=private/'handoff-data';assert (scratch/'B-kernel-gate.json').exists() and (scratch/'ui-gate.json').exists();assert not target.exists();target.mkdir();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();files=[]
for p in sorted(scratch.rglob('*')):
 if p.is_file() and not p.is_symlink():files.append(('evidence/'+str(p.relative_to(scratch)),p))
for p in sorted(private.iterdir()):
 if p.is_file() and p.suffix in ['.py','.sh','.mjs','.json','.sol','.lean','.c']:files.append(('executed-private/'+p.name,p))
for rel in ['/workspace/h62-coordinator-inputs/router-20261107T055306Z/cd333e5e80b0b4d78b9865d2cb1642aeda8d543acbcb6523043c5ea84d35f645.ticket','tests/directruntime-20261104/native-browser/fixed-byte/results-manifest.json','.lake/native-browser-serial.toml','.lake/native-browser-prefix/bin/lake']:
 p=root/rel;files.append(('intake/'+p.name,p))
index=[{'path':n,'bytes':p.stat().st_size,'sha256':sha(p)} for n,p in files];(target/'evidence-files.json').write_text(json.dumps(index,indent=2)+'\n')
with tarfile.open(target/'evidence.tar.gz','w:gz') as t:
 for n,p in files:t.add(p,arcname=n,recursive=False)
 t.add(target/'evidence-files.json',arcname='evidence-files.json')
runtime=[]
for mode,names in [('native',['direct-check','build.json']),('direct',['direct.js','direct.wasm','build.json'])]:
 for name in names:runtime.append((mode+'/'+name,private/mode/name))
(target/'runtime-files.json').write_text(json.dumps([{'path':n,'bytes':p.stat().st_size,'sha256':sha(p)} for n,p in runtime],indent=2)+'\n')
with tarfile.open(target/'runtime-artifacts.tar.gz','w:gz') as t:
 for n,p in runtime:t.add(p,arcname=n,recursive=False)
 t.add(target/'runtime-files.json',arcname='runtime-files.json')
cache=[]
for module in ['Solidity/Frontend/ExecutableAst/Shared/Translate','Solidity/Frontend/ExecutableAst/Shared/Compose','Solidity/Tools/DirectRuntime','Solidity/Tools/SourceCounterexample']:
 for sub,exts in [('lib/lean',['olean','olean.hash','ilean','ilean.hash','trace']),('ir',['c','c.hash','setup.json'])]:
  for ext in exts:
   p=root/'.lake/build'/sub/(module+'.'+ext);assert p.is_file();cache.append({'path':str(p.relative_to(root)),'bytes':p.stat().st_size,'sha256':sha(p)})
(target/'cache-files.json').write_text(json.dumps({'sourceBuildHead':'4d7285b80e89741e9da8cb49ce7ab8b62a828a72','files':cache,'boundary':'Locally retained32incremental artifacts;coordinatorpending,noVMship-cache/noH88cross-cachecoherence claim.'},indent=2)+'\n')
with tarfile.open(target/'incremental-cache.tar.gz','w:gz') as t:
 for e in cache:t.add(root/e['path'],arcname=e['path'],recursive=False)
 t.add(target/'cache-files.json',arcname='cache-files.json')
for archive,idx in [('evidence.tar.gz','evidence-files.json'),('runtime-artifacts.tar.gz','runtime-files.json'),('incremental-cache.tar.gz','cache-files.json')]:
 with tarfile.open(target/archive) as t:
  entries=json.load(t.extractfile(idx));entries=entries['files'] if isinstance(entries,dict) else entries
  for e in entries:
   b=t.extractfile(e['path']).read();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256']
print(json.dumps({p.name:{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in target.iterdir()},indent=2))
