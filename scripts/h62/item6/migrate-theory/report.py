#!/usr/bin/env python3
"""Export frozen source pins and exact-file dependency owners without source edits."""
import argparse, hashlib, json, pathlib
from census import census, source_path, ROOT
p=argparse.ArgumentParser();p.add_argument('--inputs',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
c=census();registry=json.loads((a.inputs/'ownership.json').read_text())
lanes=[x for x in registry['items'] if 'migrate-' in x.get('owner','')]
report={'base':c['base'],'assigned_count':c['assigned_count'],
 'pin_kind':'whole UTF-8 source SHA256, includes statements and proofs; not an elaborated declaration hash',
 'frozen_sources':[{'path':x['path'],'sha256':x['sha256'],'base_sha256':x['base_sha256'],'unchanged':x['unchanged']} for x in c['files']],
 'declaration_command_sites':sum(len(x['declaration_candidates']) for x in c['files']),
 'branch_line_sites':sum(len(x['branch_lines']) for x in c['files']),
 'trust_tokens':{t:sum(x['trust_tokens'][t] for x in c['files']) for t in ['sorry','axiom','native_decide']},
 'dependencies':[], 'ownership_snapshot_sha256':hashlib.sha256((a.inputs/'ownership.json').read_bytes()).hexdigest(),
 'proof_boundary':'Source scans and compilation are not a semantic-equivalence proof across Lean releases. Generated declarations and axiom closure remain final-gate obligations.'}
for mod in c['external_dependencies']:
 path=str(source_path(mod).relative_to(ROOT))
 owners=[x['owner'] for x in lanes if path in [v.strip() for v in x.get('writeScope','').split(';')]]
 report['dependencies'].append({'module':mod,'path':path,'owners':owners,'sha256':c['closure_source_sha256'][path],
 'direct_importers':[x['path'] for x in c['files'] if mod in x['imports']]})
a.output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print('FROZEN_SOURCE_PINS_PASS' if all(x['unchanged'] for x in report['frozen_sources']) else 'FROZEN_SOURCE_PINS_FAIL')
print('external_dependencies',len(report['dependencies']),'unresolved_owners',sum(not x['owners'] for x in report['dependencies']))

if not all(x['unchanged'] for x in report['frozen_sources']): raise SystemExit(1)
