#!/usr/bin/env python3
"""Non-Lean classification of saved compiler declarations; no exclusions/proofs."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

p=argparse.ArgumentParser(description=__doc__)
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
root=Path.cwd();prior=Path("/workspace/h62-audit-h70-evidence")
hashdata=lambda x:hashlib.sha256(x).hexdigest()
receipt=json.loads((prior/"h70-receipt.json").read_text())
phase=receipt["phases"]["proof"]
log=(prior/phase["log"]).read_bytes()
if hashdata(log)!=phase["log_sha256"]:raise ValueError("saved proof log drift")
raw=[]
for line in log.decode().splitlines():
 if line.startswith("MODULE_THEOREMS_JSON "):
  raw.extend(json.loads(line.split(" ",1)[1])["theorems"])
old=json.loads((prior/"h70-compiler-census.json").read_text())
lookup={r["name"]:r for r in raw}
if len(lookup)!=len(raw) or len(old)!=len(raw):raise ValueError("duplicate/missing saved declarations")
source=json.loads(Path('/workspace/h62-audit-evidence/source-census.json').read_text())
names={r['name_candidate'] for r in source['declarations'] if r['name_candidate']}
rows=[]
for entry in old:
 original=lookup[entry['name']]
 if any(entry[k]!=v for k,v in original.items()):raise ValueError('kernel census drift')
 if entry['coverage']!='uncovered_compiler_declaration':continue
 n=entry['name']
 if '._proof_' in n:kind='proof_auxiliary_name'
 elif '._simp_' in n:kind='simplifier_auxiliary_name'
 elif re.search(r'\.eq_\d+$',n):kind='numbered_equation_name'
 elif n.endswith(('.eq_def','.else_eq')):kind='definition_or_branch_equation_name'
 elif n.endswith(('.inj','.injEq')):kind='constructor_injectivity_name'
 elif n.endswith('.sizeOf_spec'):kind='size_specification_name'
 else:kind='other_name'
 parents=[s for s in names if n.startswith(s+'.')]
 parent=max(parents,key=len) if parents else None
 rows.append(dict(name=n,module=entry['module'],category=kind,
   lexical_source_theorem_parent=parent,parent_relation='name-prefix only; not dependency or ownership',
   signature_sha256=hashdata(entry['signature'].encode()),
   kernel_type_expr_sha256=hashdata(entry['kernel_type_expr'].encode()),
   witness_status='uncovered',owner='unresolved live producer',exclusion=False))
if len(rows)!=563 or len({r['name'] for r in rows})!=563:raise ValueError('partition drift')
path='Solidity/Calculus/LinearCountermodel.lean'
frozen=subprocess.check_output(['git','show','c6f550e281a7e5affa9a99bc2cdaed556dec00e4:'+path])
oldline=b"  simpa only [Bool.not_eq_true'] using hp"
newline=b"  simpa only [falseNode, Bool.not_eq_true'] using hp"
if frozen.count(oldline)!=1 or (root/path).read_bytes()!=frozen.replace(oldline,newline):
 raise ValueError('repair differs from exact authorized proof-only patch')
header=next(l for l in frozen.decode().splitlines() if l.startswith('theorem falseNode_spec ')).split(':=')[0]
result=dict(schema_version=1,source_receipt_sha256=hashdata((prior/'h70-receipt.json').read_bytes()),
 categories=dict(sorted(Counter(r['category'] for r in rows).items())),
 modules=dict(sorted(Counter(r['module'] for r in rows).items())),
 declaration_count=len(rows),witnesses_added=0,exclusions_added=0,
 repair=dict(file=path,statement_source_sha256=hashdata(header.encode()),
   original_sha256=hashdata(frozen),current_sha256=hashdata((root/path).read_bytes()),
   status='proof-only textual change; Lean and axiom validation pending STOP'),
 declarations=sorted(rows,key=lambda x:x['name']))
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='declarations'}))
