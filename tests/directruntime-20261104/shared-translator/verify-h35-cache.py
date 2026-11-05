"""Verify ship-cache's local pack without extracting it or claiming delivery."""
from pathlib import Path
import hashlib,json,subprocess,tarfile
owned=Path(__file__).resolve().parent
ship=owned/'artifacts/h35/cache-ship/20261104T222712Z-713a0612'
rows={name:(int(size),sha) for name,size,sha in (line.split('\t') for line in (ship/'artifacts.tsv').read_text().splitlines())}
packs=list(ship.glob('pack-*.tar.zst'))
assert len(packs)==1
pack=packs[0];seen=set();total=0
proc=subprocess.Popen(['zstd','-dc','--',str(pack)],stdout=subprocess.PIPE)
with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:
 for member in archive:
  assert member.isfile() and member.name in rows and member.name not in seen,member.name
  size,digest=rows[member.name];assert member.size==size
  src=archive.extractfile(member);h=hashlib.sha256()
  for chunk in iter(lambda:src.read(1024*1024),b''):h.update(chunk)
  assert h.hexdigest()==digest,member.name
  seen.add(member.name);total+=size
for chunk in iter(lambda:proc.stdout.read(1024*1024),b''):assert not chunk.strip(b'\0')
assert proc.wait()==0 and seen==set(rows)
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as src:
  for chunk in iter(lambda:src.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
prefixes={name.split('.',1)[0] for name in rows}
mappingCount=0;packageMaps={}
for path in ship.glob('inputs.*.jsonl'):
 mappings={}
 for line in path.read_text().splitlines():
  pair=json.loads(line);assert isinstance(pair,list) and len(pair)==2
  key,value=pair;assert isinstance(key,str) and key
  if isinstance(value,str):refs=[value]
  else:
   assert isinstance(value,dict) and value
   refs=[x for v in value.values() for x in (v if isinstance(v,list) else [v])]
  assert refs and all(isinstance(ref,str) and ref in prefixes for ref in refs)
  assert key not in mappings or mappings[key]==value
  mappings[key]=value;mappingCount+=1
 packageMaps[path.name]=mappings
root=owned.parents[2];ownedMappings=[]
for module in ['Solidity/Frontend/ExecutableAst/Shared/'+n for n in ['Boundary','Translate','Intrinsic']]+['Solidity/Tools/DirectRuntime']:
 trace=json.loads((root/'.lake/build/lib/lean'/Path(module+'.trace')).read_text())
 assert packageMaps['inputs.solidity-lean.jsonl'][trace['depHash']]==trace['outputs']
 source=root/(module+'.lean')
 ownedMappings.append({'module':module.replace('/','.'),'depHash':trace['depHash'],'outputs':trace['outputs'],'sourceSha256':sha(source)})
metrics=[]
for line in (owned/'artifacts/h35/ship-cache.log').read_text().splitlines():
 try:row=json.loads(line)
 except json.JSONDecodeError:continue
 if 'command' in row and 'exit' in row:metrics.append(row)
assert len(metrics)==1 and metrics[0]['exit']==1
versions=(owned/'artifacts/h35/build-mcp-fixed.log').read_text().splitlines()[:2]
assert versions[0].startswith('Lean (version 4.24.0') and versions[1].startswith('Lake version 5.0.0-src+797c613')
failure=next(line for line in (owned/'artifacts/h35/ship-cache.log').read_text().splitlines() if line.startswith('FileNotFoundError:'))
receipt={'status':'verified-local-pack; delivery-blocked','script':'scripts/coord-tools/ship-cache.sh',
 'scriptExit':metrics[0]['exit'],'scriptFailure':failure,
 'scriptDeliveryReceipt':None,'delivered':False,'implementationHead':(ship/'HEAD').read_text().strip(),
 'pack':str(pack.resolve()),'packSha256':sha(pack),'packBytes':pack.stat().st_size,'verifiedArtifacts':len(seen),
 'uncompressedArtifactBytes':total,'inputMappings':mappingCount,'mappingOutputReferencesVerified':True,'ownedModuleMappings':ownedMappings,
 'artifactManifest':str((ship/'artifacts.tsv').resolve()),'toolchainFromGateLog':versions,
 'boundary':'Every archive artifact size/SHA256 checked against the script manifest without extraction. Mapping schemas/output-prefix references and four owned source trace mappings also checked. No network transfer or installation occurred; no installed-cache or executable-closure claim.'}
(owned/'artifacts/h35/cache-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
