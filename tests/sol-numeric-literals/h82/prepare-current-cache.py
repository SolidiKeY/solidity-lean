#!/usr/bin/env python3
"""Deterministic local cache proposal. Never ships or changes historical approval."""
import argparse, gzip, hashlib, io, json, pathlib, tarfile
ap=argparse.ArgumentParser(); ap.add_argument('--output',type=pathlib.Path,required=True); a=ap.parse_args()
r=pathlib.Path(__file__).resolve().parents[3]; c=pathlib.Path('/workspace/.setup/cache/lake')
assert not a.output.resolve().is_relative_to(r.resolve()), 'output must be outside checkout'
a.output.mkdir(exist_ok=False)
expected=json.loads((r/'tests/sol-numeric-literals/acceptance.json').read_text())['modules']
assert len(expected)==42 and {m['path'] for m in expected}=={str(p.relative_to(r)) for p in (r/'Solidity/Frontend/NumericLiteralProofs').rglob('*.lean')}
for m in expected: assert hashlib.sha256((r/m['path']).read_bytes()).hexdigest()==m['sha256']
lines={}
for line in (c/'inputs/solidity-lean.jsonl').read_text().splitlines():
 try: lines[str(json.loads(line)[0])]=line
 except (ValueError,IndexError): pass
artifacts={}
for p in (c/'artifacts').iterdir(): artifacts.setdefault(p.name.split('.',1)[0],[]).append(p)
selected={}; files={}; modules=[]
for p in sorted((r/'Solidity/Frontend/NumericLiteralProofs').rglob('*.lean')):
 rel=p.relative_to(r); d=json.loads((r/'.lake/build/lib/lean'/rel.with_suffix('.trace')).read_text()); key=str(d['depHash'])
 assert json.loads(lines[key])[1]==d['outputs']; selected[key]=lines[key]
 hashes=[str(h) for v in d['outputs'].values() for h in (v if isinstance(v,list) else [v])]
 for h in hashes:
  assert h in artifacts
  for f in artifacts[h]: files['artifacts/'+f.name]=f
 modules.append(dict(module=str(rel.with_suffix('')).replace('/','.'),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),input_hash=key,output_hashes=hashes))
assert len(modules)==42 and len(selected)==42
rows=[dict(path=name,size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for name,p in sorted(files.items())]
record=dict(schema_version=1,status='prepared_not_approved_or_delivered',owned_modules=modules,mapping_count=len(selected),artifacts=rows,boundary='Observed trace/mapping proposal only: source-to-trace freshness and cache output-name hashing are not independently validated. SHA256 verifies packaged byte consistency. No current-cache acceptance, shipment or compatibility claim. Historical approved pack preserved.')
payload=json.dumps(record,indent=2).encode()+b'\n'; mapping=('\n'.join(selected[k] for k in sorted(selected))+'\n').encode()
archive=a.output/'owned-cache.tar.gz'
with archive.open('wb') as raw:
 with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0,filename='') as zipped:
  with tarfile.open(fileobj=zipped,mode='w') as tar:
   for name,data in [('manifest.json',payload),('inputs/solidity-lean.jsonl',mapping)]+[(name,p.read_bytes()) for name,p in sorted(files.items())]:
    info=tarfile.TarInfo(name); info.size=len(data); info.mode=0o644; tar.addfile(info,io.BytesIO(data))
with tarfile.open(archive,'r:gz') as tar:
 for row in rows: assert hashlib.sha256(tar.extractfile(row['path']).read()).hexdigest()==row['sha256']
summary=dict(archive=str(archive),archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),archive_bytes=archive.stat().st_size,modules=len(modules),mapping_count=len(selected),artifact_count=len(rows),status=record['status'])
(a.output/'prepared.json').write_text(json.dumps(summary,indent=2)+'\n'); print(json.dumps(summary))
