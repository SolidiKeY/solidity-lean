#!/usr/bin/env python3
"""Lexical drift accounting only; never a semantic acceptance verdict."""
import json,collections
from census import inventory,ROOT,BASE

def compare(before,after):
    def groups(rows):
        out=collections.defaultdict(list)
        for row in rows:
            label='@anonymous' if row['name'].startswith('@') else row['name']
            out[(row['path'],row['kind'],label)].append(row)
        return out
    old,new=groups(before['declarations']),groups(after['declarations'])
    rows=[]
    for key in sorted(set(old)|set(new)):
        left,right=old.get(key,[]),new.get(key,[])
        if key[2]=='@anonymous': status='anonymous-unpaired'
        elif len(left)>1 or len(right)>1: status='ambiguous-no-pairing'
        elif not left: status='added'
        elif not right: status='removed'
        elif left[0]['statement_sha256']==right[0]['statement_sha256']: status='lexical-header-equal'
        else: status='lexical-header-changed'
        rows.append(dict(key=list(key),status=status,before=left,after=right))
    return dict(schema_version=1,meaning='Lexical only. Counts classify groups; accounted_* count declaration rows. Anonymous rows are never paired. Named keys omit namespace/section context and do not establish qualified identity. Equal headers do not establish unchanged imports, context, definitions, cases, elaborated statements or proof validity; inspect full file hashes.',
                counts=dict(collections.Counter(r['status'] for r in rows)),rows=rows,
                accounted_before=sum(len(r['before']) for r in rows),accounted_after=sum(len(r['after']) for r in rows),
                before_files=before['files'],after_files=after['files'])

if __name__=='__main__':
    print(json.dumps(compare(inventory(ROOT,BASE),inventory(ROOT)),ensure_ascii=False,indent=2))
