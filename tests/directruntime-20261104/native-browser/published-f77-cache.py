"""Prepare and independently stream-verify a scoped build-cache snapshot; no transport."""
import hashlib,json,os,pathlib,subprocess,tarfile
root=pathlib.Path.cwd();out=root/'.lake/native-browser-f77-cache'
assert os.environ.get('NATIVE_BROWSER_BOUNDED_GATE')=='1'
assert not out.exists();out.mkdir()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def save(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
evidence=root/'docs/benchmarks/directruntime-2026-11-04/published-f77'
for name in ['native-build-gate','wasm-build-gate','mcp-gate','validation-gate']:
 assert json.loads((evidence/(name+'.json')).read_text())['exitCode']==0
m=json.loads((root/'.lake/native-browser-f77/native/build.json').read_text())
modules={e['module']:e['sourceSha256'] for e in m['sourceFiles']}
p=root/'Solidity/Frontend/ExecutableAst/Shared/Intrinsic.lean';modules['Solidity.Frontend.ExecutableAst.Shared.Intrinsic']=sha(p)
files={}
for module,digest in sorted(modules.items()):
 stem=module.replace('.','/');assert sha(root/(stem+'.lean'))==digest
 for prefix,suffixes in [('.lake/build/lib/lean/',['.olean','.olean.hash','.ilean','.ilean.hash','.trace']),('.lake/build/ir/',['.c','.c.hash'])]:
  for suffix in suffixes:
   name=prefix+stem+suffix;p=root/name
   assert p.is_file(),name
   files[name]={'bytes':p.stat().st_size,'sha256':sha(p)}
manifest={'sourceHead':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'publishedBase':'f77cf60d3cea8f7f1db8db29cc027532b0cd3fce','leanCommit':m['leanCommit'],'modules':modules,'files':files,'boundary':'Scoped relative build-cache snapshot, not a Lake artifact-cache catalog/delta. Build artifacts only; never an ordinary request input. No transport or coordinator adoption is claimed.'}
save(out/'manifest.json',manifest)
archive=out/'build-cache.tar.zst';members=out/'members.list';members.write_text(''.join(n+'\n' for n in files))
subprocess.run(['tar','--sort=name','--mtime=@0','--owner=0','--group=0','--numeric-owner','-I','zstd -T1 -3','-cf',str(archive),'-T',str(members)],check=True)
seen=set()
with subprocess.Popen(['zstd','-dc',str(archive)],stdout=subprocess.PIPE) as child:
 with tarfile.open(fileobj=child.stdout,mode='r|') as packed:
  for member in packed:
   assert member.isfile() and member.name in files and member.name not in seen
   h=hashlib.sha256();size=0
   with packed.extractfile(member) as f:
    for b in iter(lambda:f.read(1024*1024),b''):h.update(b);size+=len(b)
   assert {'bytes':size,'sha256':h.hexdigest()}==files[member.name];seen.add(member.name)
 assert child.wait()==0
assert seen==set(files)
for name,entry in files.items():assert sha(root/name)==entry['sha256']
report={'archive':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size,'manifest':str(out/'manifest.json'),'manifestSha256':sha(out/'manifest.json'),'modules':len(modules),'filesVerified':len(seen),'passed':True,'delivery':'coordinator-pending','format':'relative build-cache snapshot; no Lake artifact catalog','boundary':manifest['boundary']}
save(evidence/'cache-pack.json',report);print(json.dumps(report))
