#!/usr/bin/env python3
"""Prepare a verified local cache asset; this does not deliver or satisfy H35 shipment."""
import hashlib,json,pathlib,tarfile
root=pathlib.Path(__file__).resolve().parents[3];folder=root/'tests/sol-numeric-literals'
cache=pathlib.Path('/workspace/.setup/cache/lake');out=pathlib.Path('/workspace/sol-numeric-literals-h35-owned-cache');out.mkdir(exist_ok=False)
manifest=json.loads((folder/'acceptance.json').read_text());build=json.loads((folder/'evidence/h35-owned-build.json').read_text())
assert build['exit']==0 and not build['resource_stop']
assert build['proof_sources']=={m['path']:m['sha256'] for m in manifest['modules']}
lines={}
for line in (cache/'inputs/solidity-lean.jsonl').read_text().splitlines():
 try:lines[json.loads(line)[0]]=line
 except (ValueError,IndexError):pass
names={}
for p in (cache/'artifacts').iterdir():names.setdefault(p.name.split('.',1)[0],[]).append(p.name)
ship=pathlib.Path('/workspace/sol-numeric-literals-h35-cache-ship/20261104T222745Z-7bb0d3a1')
shiprows={n:(int(size),digest) for n,size,digest in (x.split('\t') for x in (ship/'artifacts.tsv').read_text().splitlines())}
selected={};artifacts=set();modules=[]
for m in manifest['modules']:
 assert hashlib.sha256((root/m['path']).read_bytes()).hexdigest()==m['sha256']
 trace=root/'.lake/build/lib/lean'/pathlib.Path(m['path']).with_suffix('.trace')
 d=json.loads(trace.read_text());key=d['depHash'];assert key in lines
 outputs=d['outputs'];assert json.loads(lines[key])[1]==outputs
 hashes=[str(h) for v in outputs.values() for h in (v if isinstance(v,list) else [v])]
 for h in hashes:assert h in names;artifacts.update(names[h])
 selected[key]=lines[key];modules.append(dict(module=m['name'],source_sha256=m['sha256'],input_hash=key,output_hashes=hashes))
assert len(modules)==42 and len(selected)==42
rows=[]
for name in sorted(artifacts):
 p=cache/'artifacts'/name;h=hashlib.sha256(p.read_bytes()).hexdigest();size=p.stat().st_size
 assert name in shiprows and shiprows[name]==(size,h)
 rows.append(dict(path='artifacts/'+name,size=size,sha256=h))
(out/'inputs.solidity-lean.jsonl').write_text(''.join(selected[k]+'\n' for k in sorted(selected)))
record=dict(status='prepared_not_delivered',remote_delivery_verified=False,owned_modules=modules,artifact_files=rows,artifact_count=len(rows),artifact_bytes=sum(r['size'] for r in rows),mapping_count=len(selected),source_proof_head='7bb0d3a1d63f9ce28ffbad0a5fdc5f3da9d08cdf',origin='All selected artifacts match the required ship-cache.sh preflight manifest; no shipment receipt exists.')
(out/'manifest.json').write_text(json.dumps(record,indent=2)+'\n')
archive=out/'owned-cache.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=1) as tar:
 for row in rows:tar.add(cache/row['path'],arcname=row['path'],recursive=False)
 tar.add(out/'inputs.solidity-lean.jsonl',arcname='inputs/solidity-lean.jsonl',recursive=False)
 tar.add(out/'manifest.json',arcname='manifest.json',recursive=False)
with tarfile.open(archive,'r:gz') as tar:
 assert len(tar.getmembers())==len(rows)+2
 for row in rows:
  stream=tar.extractfile(row['path']);assert stream is not None
  assert hashlib.sha256(stream.read()).hexdigest()==row['sha256']
record['archive']=str(archive);record['archive_sha256']=hashlib.sha256(archive.read_bytes()).hexdigest();record['archive_bytes']=archive.stat().st_size
(out/'prepared.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ('owned_modules','artifact_files')}))
