#!/usr/bin/env python3
"""Bind the12 checked telescope associations to exact frozen source slices.

This subset verifier requires no replacement ownership metadata. It does not
certify interface membership, the full census, or compiler totality.
"""
import argparse,hashlib,json,pathlib,runpy,subprocess
p=argparse.ArgumentParser();p.add_argument('--gate-dir',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--gate-record',type=pathlib.Path,required=True);p.add_argument('--source-binding',type=pathlib.Path,required=True);a=p.parse_args()
r=pathlib.Path(__file__).resolve().parents[4]; census=runpy.run_path(str(pathlib.Path(__file__).with_name('census.py')))
index=json.loads((r/'tests/h62/item2/audit-language/witness-index.json').read_text());assert len(index)==12
sources={};declarations={}
for path in sorted({row['source_id'].split(':')[0] for row in index}):
 frozen=subprocess.check_output(['git','show',census['BASE']+':'+path],cwd=r)
 assert (r/path).read_bytes()==frozen, 'target source drift: '+path
 sources[path]=hashlib.sha256(frozen).hexdigest()
 for row in census['scan'](path,frozen,[]): declarations[row['id']]=row
log=(a.gate_dir/'3.log').read_text();assert 'sorryAx' not in log
for row in index:
 declaration=declarations[row['source_id']]
 assert declaration['name_candidate']==row['target'] and declaration['signature_sha256']==row['signature_sha256']
 marker='H62_WITNESS '+row['witness']+' FOR '+row['target']
 assert log.splitlines().count(marker)==1
modules=['FeatureWitness.lean','IndependentWitness.lean','FullTelescopeWitness.lean','AbiEntryWitness.lean']
receipt=json.loads(a.gate_record.read_text())
assert receipt['exit']==0 and not receipt['resource_stop']
assert receipt['limits']==dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1)
assert receipt['minimum_parent_headroom_bytes']>=4*1024**3
paths=['tests/h62/item2/audit-language/'+name for name in modules]
assert receipt['command']==['env','GATE_LOGS='+str(a.gate_dir),'bash','scripts/coord-tools/gate.sh','per-file',*paths]
binding=json.loads(a.source_binding.read_text())
assert pathlib.Path(binding['gate_record']).resolve()==a.gate_record.resolve()
assert pathlib.Path(binding['gate_dir']).resolve()==a.gate_dir.resolve()
assert binding['gate_record_sha256']==hashlib.sha256(a.gate_record.read_bytes()).hexdigest()
expected=set(paths+['tests/h62/item2/audit-language/witness-index.json']+list(sources))
assert set(binding['before_sha256'])==set(binding['after_sha256'])==expected
assert binding['before_sha256']==binding['after_sha256']=={p:hashlib.sha256((r/p).read_bytes()).hexdigest() for p in expected}
assert (a.gate_dir/'HEAD').read_text().strip()==binding['head']
assert set(binding['log_sha256'])=={'HEAD','gates.tsv','1.log','2.log','3.log','4.log'}
for name,digest in binding['log_sha256'].items(): assert hashlib.sha256((a.gate_dir/name).read_bytes()).hexdigest()==digest
statuses=[line.split('\t') for line in (a.gate_dir/'gates.tsv').read_text().splitlines()]
assert len(statuses)==4
for row,path in zip(statuses,paths): assert row[0]=='PASS' and row[1]=='lean:'+path
checked={}
for i,name in enumerate(modules,1):
 path=r/'tests/h62/item2/audit-language'/name; text=(a.gate_dir/(str(i)+'.log')).read_text()
 assert 'sorryAx' not in text and ': error:' not in text
 checked[str(path.relative_to(r))]=hashlib.sha256(path.read_bytes()).hexdigest()
report=dict(schema_version=1,status='partial',base=census['BASE'],checked_telescope_associations=index,target_sources=sources,checked_module_sources=checked,source_binding_sha256=hashlib.sha256(a.source_binding.read_bytes()).hexdigest(),gate_record_sha256=hashlib.sha256(a.gate_record.read_bytes()).hexdigest(),gate_log_sha256={str(i)+'.log':hashlib.sha256((a.gate_dir/(str(i)+'.log')).read_bytes()).hexdigest() for i in range(1,5)},boundary='Twelve imported target telescopes and exact frozen source signatures only. Full interface census/owner classification and compiler success/totality remain unfinished.')
assert not a.output.resolve().is_relative_to(r.resolve()), 'external output required'
a.output.mkdir(exist_ok=False);payload=json.dumps(report,indent=2,sort_keys=True)+'\n';(a.output/'verified-subset.json').write_text(payload);(a.output/'SHA256SUMS').write_text(hashlib.sha256(payload.encode()).hexdigest()+'  verified-subset.json\n');print('PASS:12 exact frozen target signatures and checked whole-telescope associations; full audit remains partial')
