#!/usr/bin/env python3
"""Validate a complete Expr DAG stream and freeze types plus problem definitions.
Node fingerprints use SHA256 over full constructor data and child fingerprints;
Lean's cached Expr.hash is used only for collision-checked structural deduplication.
"""
import argparse,collections,hashlib,json
from pathlib import Path
from dag_codec import DagStore,name_ok

def collect(census,log,lean_exit):
    if lean_exit!=0: raise ValueError('INTERFACE_COMPILER_FAILED')
    rows=[];counts={};dag=DagStore(census['owned'])
    lines=log.splitlines() if isinstance(log,str) else log
    for line in lines:
        if line.startswith('H62-NODE '): dag.add(json.loads(line[len('H62-NODE '):]))
        if line.startswith('H62-INTERFACE '):
            r=json.loads(line[len('H62-INTERFACE '):])
            required={'name','name_parts','module','kind','level_params','type_root','value_root','internal'}
            kinds={'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'}
            if not isinstance(r,dict) or set(r)!=required: raise ValueError('INVALID_INTERFACE_ROW')
            if not all(isinstance(r[k],str) and r[k].strip() for k in ('name','module')) or r['kind'] not in kinds or not name_ok(r['name_parts']): raise ValueError('INVALID_INTERFACE_ROW')
            if not isinstance(r['level_params'],list) or not all(name_ok(v) for v in r['level_params']) or type(r['internal']) is not bool: raise ValueError('INVALID_INTERFACE_ROW')
            type_hash=dag.root(r['module'],r['type_root'])
            semantic=r['name'].startswith('Solkey.TestSuite.') and (r['name'].endswith('.problem') or r['name']=='Solkey.TestSuite.problems')
            if semantic and (r['kind']!='definition' or r['value_root'] is None): raise ValueError('MISSING_FROZEN_DEFINITION')
            if not semantic and r['value_root'] is not None: raise ValueError('UNEXPECTED_DEFINITION_VALUE')
            value_hash=dag.root(r['module'],r['value_root']) if semantic else None
            row={k:v for k,v in r.items() if k not in ('type_root','value_root')};row.update(type_sha256=type_hash,value_sha256=value_hash);rows.append(row)
        if line.startswith('H62-MODULE '):
            r=json.loads(line[len('H62-MODULE '):])
            if not isinstance(r,dict) or set(r)!={'module','count','nodes','schema'} or r['schema']!='expr-dag-v2': raise ValueError('INVALID_MODULE_ROW')
            if not isinstance(r['module'],str) or r['module'] not in census['owned'] or type(r['count']) is not int or r['count']<0 or type(r['nodes']) is not int or r['nodes']<0: raise ValueError('INVALID_MODULE_ROW')
            if r['module'] in counts: raise ValueError('DUPLICATE_MODULE_REPORT')
            dag.finish(r['module'])
            if dag.closed[r['module']]!=r['nodes']: raise ValueError('NODE_COUNT_MISMATCH')
            counts[r['module']]=r['count']
    if not rows or set(counts)!=set(census['owned']) or dag.hashes: raise ValueError('INCOMPLETE_INTERFACE_OUTPUT')
    if len({r['name'] for r in rows})!=len(rows): raise ValueError('DUPLICATE_DECLARATION')
    actual=collections.Counter(r['module'] for r in rows)
    if any(actual[m]!=n for m,n in counts.items()) or set(actual)-set(counts): raise ValueError('MODULE_COUNT_MISMATCH')
    names={r['name'] for r in rows}
    required={'Solkey.TestSuite.additionStorageWrite.proved','Solkey.TestSuite.storageRootReadWrite.proved','Solkey.TestSuite.additionStorageWrite.problem'}
    if not required<=names: raise ValueError('MISSING_FROZEN_REPRESENTATIVE')
    case_counts={suffix:sum(name.startswith('Solkey.TestSuite.') and name.endswith('.'+suffix) for name in names) for suffix in ('proved','problem','refuted')}
    if case_counts!={'proved':552,'problem':563,'refuted':11}: raise ValueError('FROZEN_CASE_COUNT_MISMATCH: '+str(case_counts))
    if sum(r['value_sha256'] is not None for r in rows)!=564: raise ValueError('INCOMPLETE_FROZEN_DEFINITIONS')
    canonical=''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in sorted(rows,key=lambda r:r['name']))
    return canonical,{'status':'pass','kind':'structural Expr fingerprints including binder names and canonical metadata plus problem definition values; syntax source positions normalized; proof values excluded','declarations':len(rows),'case_counts':case_counts,'semantic_definitions':564,'module_counts':dict(sorted(counts.items())),'node_counts':dag.closed,'kind_counts':dict(collections.Counter(r['kind'] for r in rows)),'axiom_names':sorted(r['name'] for r in rows if r['kind']=='axiom'),'sha256':hashlib.sha256(canonical.encode()).hexdigest()}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('census',type=Path);ap.add_argument('log',type=Path);ap.add_argument('--lean-exit',required=True,type=int);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args()
    with a.log.open() as stream: canonical,summary=collect(json.loads(a.census.read_text()),stream,a.lean_exit)
    a.out.mkdir(parents=True,exist_ok=False);(a.out/'interfaces.jsonl').write_text(canonical);(a.out/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2));print(json.dumps(summary,sort_keys=True))
