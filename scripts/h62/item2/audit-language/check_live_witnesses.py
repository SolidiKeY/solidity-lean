#!/usr/bin/env python3
"""Bind one actual bounded serial witness run to before/after source hashes."""
import argparse,hashlib,json,pathlib,re,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--label',default='h82-language-witnesses-bound');a=p.parse_args()
r=pathlib.Path(__file__).resolve().parents[4];assert re.fullmatch(r'[A-Za-z0-9_-]+',a.label)
assert not a.output.resolve().is_relative_to(r.resolve());a.output.mkdir(exist_ok=False)
index='tests/h62/item2/audit-language/witness-index.json';rows=json.loads((r/index).read_text())
modules=['tests/h62/item2/audit-language/'+n for n in ['FeatureWitness.lean','IndependentWitness.lean','FullTelescopeWitness.lean','AbiEntryWitness.lean']]
paths=sorted(set(modules+[index]+[row['source_id'].split(':')[0] for row in rows]))
def snapshot():return {p:hashlib.sha256((r/p).read_bytes()).hexdigest() for p in paths}
before=snapshot();head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
evidence=pathlib.Path('/workspace/sol-numeric-literals-gate-output');record=evidence/(a.label+'.json');logs=evidence/(a.label+'-files');assert not record.exists() and not logs.exists()
command=[sys.executable,str(r/'tests/sol-numeric-literals/runtime/check.py'),a.label,'env','GATE_LOGS='+str(logs),'bash','scripts/coord-tools/gate.sh','per-file',*modules]
code=subprocess.run(command,cwd=r).returncode;after=snapshot();assert before==after
assert code==0 and json.loads(record.read_text())['exit']==0
assert (logs/'HEAD').read_text().strip()==head
payload=dict(schema_version=1,before_sha256=before,after_sha256=after,head=head,gate_record=str(record),gate_record_sha256=hashlib.sha256(record.read_bytes()).hexdigest(),gate_dir=str(logs),log_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(logs.iterdir()) if p.is_file()},boundary='Actual individual-module checks on live toolchain; no full census or compiler-totality claim.')
(a.output/'source-binding.json').write_text(json.dumps(payload,indent=2)+'\n');print('Bound before/after sources to successful four-file gate')
