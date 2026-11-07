"""Prepare and independently verify an owned-module cache delta; no network shipment."""
from pathlib import Path
import hashlib,json,subprocess,tarfile
root=Path(__file__).resolve().parents[3];owned=Path(__file__).resolve().parent
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
out=owned/'artifacts/cache-packs'/head[:12];out.mkdir(parents=True,exist_ok=True)
cache=Path('/workspace/.setup/cache/lake/artifacts')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
modules=['Solidity/Frontend/ExecutableAst/Shared/'+n for n in ['Boundary','Translate','Scope','Compose','Intrinsic']]+['Solidity/Tools/DirectRuntime']+['Solidity/Frontend/ExecutableAst/ControlTuple/'+n for n in ['Adapter','AdmissionControls','IntrinsicControls']]
mappings={};sources=[];files={}
allMaps=dict(json.loads(x) for x in Path('/workspace/.setup/cache/lake/inputs/solidity-lean.jsonl').read_text().splitlines())
for module in modules:
 trace=root/'.lake/build/lib/lean'/Path(module+'.trace');t=json.loads(trace.read_text())
 assert allMaps[t['depHash']]==t['outputs']
 mappings[t['depHash']]=t['outputs']
 sources.append({'module':module.replace('/','.'),'sourceSha256':sha(root/(module+'.lean')),'traceSha256':sha(trace),'depHash':t['depHash'],'outputs':t['outputs']})
 for ext,values in t['outputs'].items():
  for value in values if isinstance(values,list) else [values]:
   suffix={'o':'olean','i':'ilean','c':'c'}[ext];p=cache/(value+'.'+suffix);assert p.is_file()
   files[p.name]={'size':p.stat().st_size,'sha256':sha(p)}
(out/'inputs.solidity-lean.jsonl').write_text(''.join(json.dumps([k,v])+'\n' for k,v in mappings.items()))
(out/'artifacts.tsv').write_text(''.join(f"{n}\t{v['size']}\t{v['sha256']}\n" for n,v in sorted(files.items())))
pack=out/'owned-delta.tar.zst'
with pack.open('wb') as target:
 proc=subprocess.Popen(['zstd','-q','-T1','-3','-c'],stdin=subprocess.PIPE,stdout=target)
 with tarfile.open(fileobj=proc.stdin,mode='w|') as archive:
  for name in sorted(files):archive.add(cache/name,arcname=name,recursive=False)
 proc.stdin.close();assert proc.wait()==0
proc=subprocess.Popen(['zstd','-dc',str(pack)],stdout=subprocess.PIPE);seen=set()
with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:
 for member in archive:
  assert member.isfile() and member.name in files and member.name not in seen
  expected=files[member.name];assert member.size==expected['size'];h=hashlib.sha256();src=archive.extractfile(member)
  for chunk in iter(lambda:src.read(1048576),b''):h.update(chunk)
  assert h.hexdigest()==expected['sha256'];seen.add(member.name)
for chunk in iter(lambda:proc.stdout.read(1048576),b''):assert not chunk.strip(b'\0')
assert proc.wait()==0 and seen==set(files)
r={'status':'verified-local; coordinator-pending','head':head,'pack':str(pack),'sha256':sha(pack),'bytes':pack.stat().st_size,'verifiedArtifacts':len(files),'inputMappings':len(mappings),'modules':sources,'boundary':'Owned nine-module delta only. Requires matching dependency caches/toolchain; not a standalone installation, transfer receipt or native closure proof. No ship-cache.sh invocation.'}
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
