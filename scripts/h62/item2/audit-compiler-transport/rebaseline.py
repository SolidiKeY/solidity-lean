#!/usr/bin/env python3
"""Versioned source inventory across the authorized re-baseline.

Never overwrites the original frozen criterion or transfers old Lean proof
status to a new source/dependency tree. Bulk snapshots remain outside Git.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
from census import BASE, MAP, declarations, digest

def git(root,*args):
    return subprocess.check_output(['git',*args],cwd=root)

def snapshot(root,ref):
    commit=git(root,'rev-parse',ref+'^{commit}').decode().strip()
    table=git(root,'show',commit+':'+MAP)
    paths=['Solidity/'+p for p in re.findall(r'(?m)^\| `([^`]+\.lean)` \|',table.decode())]
    assert len(paths)==len(set(paths)), 'duplicate module-map entry'
    modules=[];statements=[]
    for path in paths:
        body=git(root,'show',commit+':'+path)
        rows=declarations(body.decode(),path)
        for row in rows:
            row['source_scan_witness_status']=row.pop('witness_status')
            row['witness_status']='unproved source inventory; no Lean status inferred'
        modules.append({'module':path,'sha256':digest(body),'theorems':len(rows)})
        statements.extend(rows)
    assert len({r['id'] for r in statements})==len(statements)
    return {'schema_version':1,'commit':commit,'map_sha256':digest(table),'modules':modules,
            'statements':statements,'summary':{'modules':len(modules),'source_theorems':len(statements),
             'public':sum(r['visibility']!='private' for r in statements),'private':sum(r['visibility']=='private' for r in statements)},
            'boundary':'Lexical source evidence only. Exact source/type-prefix bytes retained; Lean elaboration, semantic domains and witnesses remain separate. Equation-arm boundary requires elaborated fidelity review.'}

def compare(original,current):
    old={r['id']:r for r in original['statements']};new={r['id']:r for r in current['statements']}
    om={r['module']:r for r in original['modules']};nm={r['module']:r for r in current['modules']}
    changes=[]
    for key in sorted(old.keys() & new.keys()):
        # Full module identity also preserves local definitions, namespace and
        # notation context. It does not authenticate transitive dependencies.
        same_file=om[old[key]['module']]['sha256']==nm[new[key]['module']]['sha256']
        same_signature=old[key]['signature_sha256']==new[key]['signature_sha256']
        changes.append({'id':key,'source_name':new[key]['source_name'],'owner':new[key]['owner'],
                        'same_signature_bytes':same_signature,'same_module_bytes':same_file,
                        'current_witness_status':'pending current-tree Lean replay and semantic/domain audit'})
    added=[dict(new[k],current_witness_status='uncovered; newly mapped source theorem; no inherited proof status') for k in sorted(new.keys()-old.keys())]
    removed=[old[k] for k in sorted(old.keys()-new.keys())]
    return {'schema_version':1,'original_base':original['commit'],'current_base':current['commit'],
            'summary':{'original_modules':len(om),'current_modules':len(nm),'original_theorems':len(old),
             'current_theorems':len(new),'retained':len(changes),'unchanged_signatures':sum(r['same_signature_bytes'] for r in changes),
             'unchanged_module_bytes':sum(r['same_module_bytes'] for r in changes),'added':len(added),'removed':len(removed)},
            'added_modules':sorted(nm.keys()-om.keys()),'removed_modules':sorted(om.keys()-nm.keys()),
            'retained':changes,'added':added,'removed':removed,
            'historical_evidence_boundary':'Original1134 proof constants/498 uncovered/91 producer obligations stay historical, not current replay counts. H69 classification remains explicit; no new exclusion or impossibility classification inferred.',
            'current_validation':'pending Lean census/replay and global-versus-input classification; source-only re-baseline is not proof completion'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path.cwd())
    ap.add_argument('--ref',required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();root=a.root.resolve();a.output.mkdir(parents=True,exist_ok=True)
    original=snapshot(root,BASE);current=snapshot(root,a.ref);result=compare(original,current)
    for module in current['modules']:
        assert digest((root/module['module']).read_bytes())==module['sha256'], 'working tree differs from selected baseline: '+module['module']
    assert digest((root/MAP).read_bytes())==current['map_sha256'], 'working module map differs'
    for filename,value in [('original-source.json',original),('current-source.json',current),('source-transition.json',result)]:
        (a.output/filename).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result['summary'],sort_keys=True))
    print('PASS versioned source inventory; no Lean proof status promoted across baselines')

if __name__=='__main__':main()
