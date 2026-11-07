#!/usr/bin/env python3
"""Join complete old name inventory to frozen signatures; never infer new parity.
Every compiler extra and internal/private name is retained. No generated family
is excluded. Missing kernel names, duplicate rows, counts and tampered snapshots
fail closed. Compiler-only signatures stay explicitly unresolved for root review.
"""
import argparse,collections,hashlib,json,re
from dag_codec import name_ok
from pathlib import Path

def artifact_location(value,root,recorded_root=None):
    root=Path(root).resolve();path=Path(value)
    if path.is_absolute():path=path.relative_to(Path(recorded_root or root))
    if '..' in path.parts:raise ValueError('ARTIFACT_PATH_ESCAPES_ROOT')
    resolved=(root/path).resolve()
    if not resolved.is_relative_to(root):raise ValueError('ARTIFACT_PATH_ESCAPES_ROOT')
    return resolved

def name_flags(parts):
    private=False;internal=False
    while parts!=['anonymous']:
        if parts[0]=='str':
            private=private or parts==['str',['anonymous'],'_private']
            internal=internal or parts[2].startswith('_')
        parts=parts[1]
    return private,internal

def hash_ok(value): return isinstance(value,str) and re.fullmatch('[0-9a-f]{64}',value) is not None

def report(census,interfaces,manifest,lines,lean_exit):
    if lean_exit!=0: raise ValueError('INVENTORY_COMPILER_FAILED')
    digest=hashlib.sha256(interfaces.encode()).hexdigest()
    if manifest.get('status')!='pass' or manifest.get('sha256')!=digest: raise ValueError('UNVERIFIED_SIGNATURE_SNAPSHOT')
    types=[json.loads(line) for line in interfaces.splitlines()]
    required={'module','name','kind','name_parts','level_params','internal','type_sha256','value_sha256'}
    for r in types:
        if not isinstance(r,dict) or set(r)!=required or not isinstance(r['module'],str) or r['module'] not in census['owned'] or not isinstance(r['name'],str) or not r['name'] or r['kind'] not in {'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'} or not name_ok(r['name_parts']) or not isinstance(r['level_params'],list) or not all(name_ok(v) for v in r['level_params']) or type(r['internal']) is not bool or not hash_ok(r['type_sha256']) or (r['value_sha256'] is not None and not hash_ok(r['value_sha256'])):
            raise ValueError('INVALID_SIGNATURE_ROW')
        if name_flags(r['name_parts'])[1]!=r['internal']: raise ValueError('SIGNATURE_NAME_FLAG_MISMATCH')
    names={(r['module'],r['name']):r for r in types}
    if len(names)!=len(types) or len(types)!=manifest.get('declarations'): raise ValueError('SIGNATURE_COUNT_MISMATCH')
    if set(census['owned'])!=set(manifest['module_counts']): raise ValueError('SIGNATURE_MODULE_MISMATCH')
    rows={};counts={}
    for line in lines:
        if line.startswith('H62-API '):
            r=json.loads(line[len('H62-API '):])
            if set(r)!={'module','name','name_parts','category','private','internal'} or r['module'] not in census['owned'] or not isinstance(r['name'],str) or not r['name'] or r['category'] not in ('kernel','compiler_extra') or not name_ok(r['name_parts']) or type(r['private']) is not bool or type(r['internal']) is not bool: raise ValueError('INVALID_API_ROW')
            if name_flags(r['name_parts'])!=(r['private'],r['internal']): raise ValueError('NAME_FLAG_MISMATCH')
            key=(r['module'],r['category'],r['name'])
            if key in rows: raise ValueError('DUPLICATE_API_ROW')
            signature=names.get((r['module'],r['name']))
            if r['category']=='kernel' and signature is None: raise ValueError('MISSING_KERNEL_SIGNATURE')
            if r['category']=='compiler_extra' and signature is not None: raise ValueError('CROSS_CATEGORY_NAME_OVERLAP')
            if signature and signature['name_parts']!=r['name_parts']: raise ValueError('SIGNATURE_NAME_MISMATCH')
            r.update(old_signature=({'kind':signature['kind'],'name_parts':signature['name_parts'],'level_params':signature['level_params'],'type_sha256':signature['type_sha256'],'format':'expr-dag-v2'} if signature else None),new_signature=None,shim_signature=None,shim_name=None,export_visibility='unresolved',signature_status=('old_kernel_signature_recorded_new_pending' if signature else 'compiler_extra_signature_unresolved'),excluded=False)
            rows[key]=r
        elif line.startswith('H62-API-MODULE '):
            r=json.loads(line[len('H62-API-MODULE '):]);m=r.get('module')
            if set(r)!={'module','kernel','compiler_extra'} or m not in census['owned'] or m in counts or any(type(r[k]) is not int or r[k]<0 for k in ('kernel','compiler_extra')): raise ValueError('INVALID_API_MODULE')
            counts[m]=r
    if set(counts)!=set(census['owned']): raise ValueError('INCOMPLETE_API_MODULES')
    kernel={(m,n) for m,c,n in rows if c=='kernel'}
    if kernel!=set(names): raise ValueError('INCOMPLETE_KERNEL_INVENTORY')
    for m,c in counts.items():
        for category in ('kernel','compiler_extra'):
            if sum(key[0]==m and key[1]==category for key in rows)!=c[category]: raise ValueError('INVENTORY_COUNT_MISMATCH')
        if c['kernel']!=manifest['module_counts'][m]: raise ValueError('SIGNATURE_COUNT_MISMATCH')
    ordered=[rows[k] for k in sorted(rows)]
    canonical=''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in ordered)
    summary={'status':'old_inventory_recorded_new_parity_pending','modules':len(counts),'kernel_declarations':len(kernel),'compiler_extra_names':sum(r['category']=='compiler_extra' for r in ordered),'unresolved_old_signatures':sum(r['old_signature'] is None for r in ordered),'name_classification':dict(collections.Counter('private' if r['private'] else 'nonprivate_internal' if r['internal'] else 'nonprivate' for r in ordered)),'exclusions':0,'implemented_shims':[],'old_snapshot_sha256':digest,'inventory_sha256':hashlib.sha256(canonical.encode()).hexdigest(),'boundary':'Name flags classify encoding, not export accessibility. Complete enumerated kernel+compiler-extra names from old ModuleData only. No new parity or exhaustive H78 acceptance. Exact structural types require referenced accepted DAG stream; no printed-signature or transitive-semantic equivalence claim.'}
    return canonical,summary

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--census',type=Path,required=True);ap.add_argument('--interfaces',type=Path,required=True);ap.add_argument('--manifest',type=Path,required=True);ap.add_argument('--log',type=Path,required=True);ap.add_argument('--lean-exit',type=int,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--compiler-summary',type=Path,required=True);ap.add_argument('--dag-log',type=Path,required=True);ap.add_argument('--artifact-root',type=Path,required=True);ap.add_argument('--recorded-root',type=Path);a=ap.parse_args()
    compiler=json.loads(a.compiler_summary.read_text())
    if compiler.get('status')!='pass' or compiler.get('exit')!=0 or compiler.get('stop') is not None or a.lean_exit!=0 or artifact_location(compiler['log'],a.artifact_root,a.recorded_root)!=a.log.resolve(): raise ValueError('UNVERIFIED_INVENTORY_COMPILATION')
    versions=compiler.get('versions',{})
    if versions.get('lean')!='Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)' or versions.get('lake')!='Lake version 5.0.0-src+797c613 (Lean version 4.24.0)': raise ValueError('WRONG_OLD_TOOLCHAIN')
    if hashlib.sha256(artifact_location(compiler['command'][-1],a.artifact_root,a.recorded_root).read_bytes()).hexdigest()!=compiler['fixture_sha256']: raise ValueError('INVENTORY_FIXTURE_CHANGED')
    with a.log.open() as stream: canonical,summary=report(json.loads(a.census.read_text()),a.interfaces.read_text(),json.loads(a.manifest.read_text()),stream,a.lean_exit)
    summary['provenance']={label:{'path':path.resolve().relative_to(a.artifact_root.resolve()).as_posix(),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()} for label,path in [('census',a.census),('old_signatures',a.interfaces),('old_signature_manifest',a.manifest),('inventory_log',a.log),('compiler_summary',a.compiler_summary),('old_signature_dag_stream',a.dag_log)]}
    summary['artifact_root']='.'
    summary['versions']=versions
    a.out.mkdir(parents=True,exist_ok=False);(a.out/'inventory.jsonl').write_text(canonical);(a.out/'summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary))
