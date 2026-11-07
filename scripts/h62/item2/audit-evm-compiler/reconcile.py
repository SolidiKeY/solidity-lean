#!/usr/bin/env python3
"""Join frozen source candidates with inspected constants; fail on ambiguities.
No binder is classified as feasible merely because its type is Prop/Type.
"""
import argparse, collections, fnmatch, hashlib, json, pathlib
p=argparse.ArgumentParser(); p.add_argument('--source',required=True); p.add_argument('--kernel',required=True); p.add_argument('--output',required=True); p.add_argument('--ownership',required=True); p.add_argument('--coverage',required=True); p.add_argument('--additional-coverage',action='append',default=[]); a=p.parse_args()
x=json.loads(pathlib.Path(a.source).read_text()); kernel=[json.loads(line) for line in pathlib.Path(a.kernel).read_text().splitlines() if line.startswith('{')]
def normalize(s):return s.replace('«','').replace('»','')
def module(file):return file.removeprefix('Bridge/').removesuffix('.lean').replace('/','.')
index=collections.defaultdict(list)
for row in kernel:index[(row['module'],normalize(row['source_user_name']))].append(row)
ownership_bytes=pathlib.Path(a.ownership).read_bytes(); ownership=json.loads(ownership_bytes)
x['ownership_snapshot_sha256']=hashlib.sha256(ownership_bytes).hexdigest()
matched=set(); counts=collections.Counter()
for row in x['statements']:
    row['statement_id']=row['file']+':'+str(row['line'])
    matches=index[(module(row['file']),normalize(row['candidate_name']))]
    if len(matches)>1:raise ValueError('ambiguous kernel matching: '+row['statement_id'])
    if matches:
        k=matches[0]; row['kernel']=k; row['kernel_type_sha256']=hashlib.sha256(k['type_expr'].encode()).hexdigest(); row['kernel_status']='type-extracted-not-witnessed'
        matched.add((k['module'],k['name'])); counts['types_extracted']+=1
    else:row['kernel_status']='pending'; counts['types_pending']+=1
    row['global_versus_per_input_classification']='pending'
    row['simultaneous_witness']='pending'
    row['producer_owner']=None
    row['write_owner_candidates']=[]
    row['migration_overlay_candidates']=[]
    for item in ownership['items']:
        scope=item.get('writeScope','')
        if not isinstance(scope,str): continue
        patterns=[part.strip().rstrip('/') for part in scope.split(';')]
        if any(row['file']==pat or fnmatch.fnmatchcase(row['file'],pat) or pat.endswith('/**') and row['file'].startswith(pat[:-2]) for pat in patterns):
            candidate=dict(id=item['id'],owner=item.get('owner'),snapshot_status=item.get('status'))
            field='migration_overlay_candidates' if item['id'].startswith('H62-6-') else 'write_owner_candidates'
            row[field].append(candidate)
x['reconciliation_summary']=dict(counts)
public=collections.defaultdict(list)
for row in x['statements']:
    if row['visibility']=='public-source':public[row['candidate_name']].append(row['statement_id'])
x['duplicate_public_source_candidates']={name:ids for name,ids in public.items() if len(ids)>1}
x['unmapped_kernel_constants']=[dict(module=r['module'],name=r['name']) for r in kernel if (r['module'],r['name']) not in matched]
coverage=json.loads(pathlib.Path(a.coverage).read_text())
if coverage['base']!=x['base']:raise ValueError('coverage base mismatch')
for extra_path in a.additional_coverage:
    extra=json.loads(pathlib.Path(extra_path).read_text())
    if extra['base']!=x['base']:raise ValueError('additional coverage base mismatch')
    coverage['links'].extend(extra['links'])
by_id={r['statement_id']:r for r in x['statements']}; seen=set()
for link in coverage['links']:
    key=link['statement_id']
    if key in seen:raise ValueError('duplicate coverage link')
    seen.add(key); row=by_id[key]
    if row['source_signature_sha256']!=link['source_signature_sha256'] or row['candidate_name']!=link['original']:raise ValueError('frozen coverage statement mismatch')
    row['simultaneous_witness']=link['status'];row['audit_proof']=link['proof'];row['audit_module']=link['module'];row['global_versus_per_input_classification']=link['classification']
    if link.get('producer_owner'):
        row['producer_owner']=link['producer_owner'];row['owner_authority']=link['owner_authority']
x['witness_coverage']=dict(collections.Counter(r['simultaneous_witness'] for r in x['statements']))
x['kernel_verified']=False
pathlib.Path(a.output).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n'); print(json.dumps(dict(counts)))
