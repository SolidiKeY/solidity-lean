#!/usr/bin/env python3
"""Validate full compiler output and emit a canonical frozen raw-type hash."""
import argparse,collections,hashlib,json
from pathlib import Path

def collect(census,log,lean_exit):
    if lean_exit!=0: raise ValueError('INTERFACE_COMPILER_FAILED')
    rows=[];counts={}
    for line in log.splitlines():
        if line.startswith('H62-INTERFACE '):
            r=json.loads(line[len('H62-INTERFACE '):])
            kinds={'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'}
            if not isinstance(r,dict) or not {'name','module','kind','levels','raw_type','internal'}<=set(r): raise ValueError('INVALID_INTERFACE_ROW')
            if not all(isinstance(r[k],str) and r[k].strip() for k in ('name','module','raw_type')) or r['kind'] not in kinds: raise ValueError('INVALID_INTERFACE_ROW')
            if not isinstance(r['levels'],list) or not all(isinstance(v,str) for v in r['levels']) or type(r['internal']) is not bool: raise ValueError('INVALID_INTERFACE_ROW')
            rows.append(r)
        if line.startswith('H62-MODULE '):
            r=json.loads(line[len('H62-MODULE '):])
            if not isinstance(r,dict) or not isinstance(r.get('module'),str) or type(r.get('count')) is not int or r['count']<0: raise ValueError('INVALID_MODULE_ROW')
            if r['module'] in counts: raise ValueError('DUPLICATE_MODULE_REPORT')
            counts[r['module']]=r['count']
    if not rows or set(counts)!=set(census['owned']): raise ValueError('INCOMPLETE_INTERFACE_OUTPUT')
    if len({r['name'] for r in rows})!=len(rows): raise ValueError('DUPLICATE_DECLARATION')
    actual=collections.Counter(r['module'] for r in rows)
    if any(actual[m]!=n for m,n in counts.items()) or set(actual)-set(counts): raise ValueError('MODULE_COUNT_MISMATCH')
    names={r['name'] for r in rows}
    required={'Solkey.TestSuite.additionStorageWrite.proved','Solkey.TestSuite.storageRootReadWrite.proved','Solkey.TestSuite.additionStorageWrite.problem'}
    if not required<=names: raise ValueError('MISSING_FROZEN_REPRESENTATIVE')
    canonical=''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in sorted(rows,key=lambda r:r['name']))
    return canonical,{'status':'pass','kind':'version-sensitive raw types/kinds/levels; no proof-value or semantic equivalence claim','declarations':len(rows),'module_counts':dict(sorted(counts.items())),'kind_counts':dict(collections.Counter(r['kind'] for r in rows)),'sha256':hashlib.sha256(canonical.encode()).hexdigest()}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('census',type=Path);ap.add_argument('log',type=Path);ap.add_argument('--lean-exit',required=True,type=int);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args()
    canonical,summary=collect(json.loads(a.census.read_text()),a.log.read_text(),a.lean_exit)
    a.out.mkdir(parents=True,exist_ok=False);(a.out/'interfaces.jsonl').write_text(canonical);(a.out/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2));print(json.dumps(summary,sort_keys=True))
