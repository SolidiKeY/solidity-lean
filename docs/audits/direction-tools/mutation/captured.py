#!/usr/bin/env python3
"""Verify coordinator archive and analyze captured records; never execute Lean/solc/EVM.
Reproduce: python3 docs/audits/direction-tools/mutation/captured.py ARCHIVE --extract OUTSIDE_CHECKOUT
"""
import argparse, collections, hashlib, json, tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
ARCHIVE_SHA='0389822b7ea06dbe7068896e38aa3abbdfe7c56376d631061efefea0bfd6a881'
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('archive',type=Path);ap.add_argument('--extract',type=Path,required=True);a=ap.parse_args()
 dest=a.extract.resolve();assert not dest.is_relative_to(ROOT),'extract outside checkout'
 assert sha(a.archive.read_bytes())==ARCHIVE_SHA,'archive hash mismatch'
 with tarfile.open(a.archive,'r:gz') as t:
  members=t.getmembers();names=[m.name for m in members]
  assert len(set(names))==len(names),'duplicate archive paths'
  assert all(m.isfile() and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts for m in members),'unsafe archive member'
  blobs={m.name:t.extractfile(m).read() for m in members}
 manifest=json.loads(blobs['delivery-manifest.json'])
 assert set(blobs)==set(manifest['files'])|{'delivery-manifest.json'},'manifest file-set mismatch'
 for name,expected in manifest['files'].items():assert sha(blobs[name])==expected, name
 # No bytes are extracted or analyzed until every delivery hash has passed.
 for name,data in blobs.items():
  target=dest/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 report=json.loads(blobs['evidence/typed-differential.json'])
 bindings={'producer_input_sha256':'evidence/typed-cases.jsonl','build_receipt_sha256':'evidence/lean/results.json','producer_sources_sha256':'evidence/producer-sources.json'}
 for key,name in bindings.items():assert report[key]==sha(blobs[name]),key
 assert report['reference_lock_sha256']==manifest['historical_reference_lock_sha256']
 assert report['reference_lock_sha256']!=manifest['rejected_current_reference_lock_sha256']
 assert not any('lock' in name.lower() for name in blobs),'unexpected lock; review provenance before accepting'
 inputs=[json.loads(x) for x in blobs['evidence/typed-cases.jsonl'].splitlines() if x.strip()]
 by_id={x['index']:x for x in inputs};assert len(by_id)==len(inputs)
 rows=report['results'];seen=set();counts=collections.Counter();classes=collections.Counter();modes=collections.Counter();families=collections.Counter();halts=collections.Counter()
 for r in rows:
  key=(r['index'],r['mode']);assert key not in seen;seen.add(key);record=by_id[r['index']]
  assert r['mode'] in ('legacy','via-ir')
  request=json.loads(blobs['typed-compiled/%s-%s.input.json'%key]);compiled=json.loads(blobs['typed-compiled/%s-%s.json'%key])
  assert request['sources']['typed.sol']['content']==record['source']
  assert request['settings']['viaIR']==(r['mode']=='via-ir')
  assert request['settings']['evmVersion']=='osaka'
  assert not any(x['severity']=='error' for x in compiled.get('errors',[]))
  assert r['source_sha256']==sha(record['source'].encode())
  compact=json.dumps(request,separators=(',',':'),ensure_ascii=False).encode();assert r['input_sha256']==sha(compact)
  for field in ['seed','kind','a','b']:assert r[field]==record[field]
  diffs=sorted(k for k in ['halt','output','storage_full','logs','rollback'] if r['expected'][k]!=r['actual'][k])
  assert sorted(r['fields'])==diffs
  status='mismatch' if diffs else 'match';assert r['status']==status
  counts[status]+=1;classes.update(diffs);modes[r['mode']]+=1;families[str(r['kind'])]+=1;halts[r['actual']['halt']]+=1
 assert seen=={(x['index'],mode) for x in inputs for mode in ['legacy','via-ir']}
 assert dict(counts)==report['counts'] and len(rows)==report['expected']
 sources=json.loads(blobs['evidence/producer-sources.json']);drift=[]
 for name,digest in sources['source_sha256'].items():
  if not (ROOT/name).exists() or sha((ROOT/name).read_bytes())!=digest:drift.append(name)
 result=dict(archive_sha256=ARCHIVE_SHA,manifest_files_verified=len(manifest['files']),report_bindings_verified=len(bindings),source_inputs=len(inputs),captured_comparisons=len(rows),counts=dict(counts),modes=dict(modes),families=dict(families),captured_halts=dict(halts),captured_agreement=counts['match']/len(rows),disagreement_classes=dict(classes),producer_base=sources['base'],producer_sources_changed_vs_audit_checkout=drift,reference_environment_reproduction='UNVERIFIABLE',historical_reference_lock_sha256=report['reference_lock_sha256'],excluded_current_reference_lock_sha256=manifest['rejected_current_reference_lock_sha256'],per_input_time_ratios=None,scope='Historical captured observation analysis only; no fresh execution, theorem validation, source runtime rebuild or full G52 qualification',limitations=manifest['limitations'])
 data=json.dumps(result,indent=2,sort_keys=True)+'\n';assert len(data.encode())<1000000
 (OUT/'captured-results.json').write_text(data);print(data)
if __name__=='__main__':main()
