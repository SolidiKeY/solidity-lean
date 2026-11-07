"""Verify every packed cache artifact without loading Lean environments."""
import hashlib,json,pathlib,subprocess,tarfile
root=pathlib.Path.cwd();shipment=root/'.lake/native-browser-h35-cache-ship/20261104T222539Z-65e23115'
output=root/'docs/benchmarks/directruntime-2026-11-04/h35/cache-pack-verification.json'
if output.exists():raise SystemExit('refusing verification receipt overwrite')
expected={}
for line in (shipment/'artifacts.tsv').read_text().splitlines():
 name,size,digest=line.split('\t');expected[name]=(int(size),digest)
packs=list(shipment.glob('pack-*.tar.zst'));assert len(packs)==1;pack=packs[0]
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
seen=set();total=0
with subprocess.Popen(['zstd','-dc',str(pack)],stdout=subprocess.PIPE) as child:
 with tarfile.open(fileobj=child.stdout,mode='r|') as archive:
  for member in archive:
   assert member.isfile() and member.name in expected and member.name not in seen
   assert pathlib.PurePosixPath(member.name).name==member.name
   h=hashlib.sha256();size=0
   with archive.extractfile(member) as f:
    for block in iter(lambda:f.read(1024*1024),b''):h.update(block);size+=len(block)
   assert (size,h.hexdigest())==expected[member.name]
   seen.add(member.name);total+=size
 assert child.wait()==0
assert seen==set(expected)
prefixes={name.split('.',1)[0] for name in seen};mappings=0
for path in shipment.glob('inputs.*.jsonl'):
 keys=set()
 for line in path.read_text().splitlines():
  key,value=json.loads(line);assert key not in keys;keys.add(key)
  hashes=[value] if isinstance(value,str) else [x for v in value.values() for x in (v if isinstance(v,list) else [v])]
  assert hashes and all(str(h) in prefixes for h in hashes);mappings+=1
report=dict(pack=str(pack),packSha256=sha(pack),packBytes=pack.stat().st_size,artifactManifest=str(shipment/'artifacts.tsv'),artifactManifestSha256=sha(shipment/'artifacts.tsv'),artifactsVerified=len(seen),artifactBytes=total,mappingsVerified=mappings,shipmentHead=(shipment/'HEAD').read_text().strip(),passed=True,remoteShipmentVerified=False,shippedMarkerExists=(shipment/'shipped').exists(),boundary='Prepared local cache pack and mapping closure verified byte-for-byte. No Lean serialized environment is loaded by verification. This is not a successful remote cache receipt.')
with output.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
