#!/usr/bin/env python3
"""Compare static import boundaries for the original assigned Yul source scope.
Current additions are read-only observations, not an ownership/scope extension.
"""
import argparse,hashlib,json,pathlib,subprocess

def sha(path):return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['root','original-census','current-census','output']:p.add_argument('--'+key,type=pathlib.Path,required=True)
    a=p.parse_args();root=a.root.resolve()
    if a.output.exists():raise SystemExit('output must be fresh')
    if sha(a.original_census)!='fac7f44fac55ba732eeb9b6151a0f001ddc4dd6d0cf10558642ffd1c30b22902':raise SystemExit('requires exact original pinned census')
    original=json.loads(a.original_census.read_text());current=json.loads(a.current_census.read_text());assigned=set(original['yul_modules'])
    if len(assigned)!=1774:raise SystemExit('original scope count mismatch')
    for row in current['modules'].values():
        if sha(root/row['path'])!=row['sha256']:raise SystemExit('current census/source drift: '+row['path'])
    def edges(census):
        return sorted((row['importer'],row['dependency']) for row in census['boundary_imports'] if row['importer'] in assigned)
    old_edges=set(edges(original));new_edges=set(edges(current))
    dependencies=sorted({dependency for _,dependency in old_edges|new_edges})
    modules=[]
    for module in dependencies:
        old=original['modules'].get(module);new=current['modules'].get(module)
        modules.append(dict(module=module,path=(new or old)['path'] if (new or old) else None,source_in_project_census=bool(new or old),old_sha256=old['sha256'] if old else None,current_sha256=new['sha256'] if new else None,source_changed=(old is None or new is None or old['sha256']!=new['sha256']) if (old or new) else None,old_importers=sorted(importer for importer,dependency in old_edges if dependency==module),current_importers=sorted(importer for importer,dependency in new_edges if dependency==module)))
    changed=sorted(module for module,row in original['modules'].items() if module not in current['modules'] or row['sha256']!=current['modules'][module]['sha256'])
    report=dict(schema_version=1,status='pass',scope='static boundary/source integrity only',base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4',source_checkpoint_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),repository=str(root),original_census_sha256=sha(a.original_census),current_census_sha256=sha(a.current_census),generator_sha256=sha(__file__),assigned_original_yul_modules=len(assigned),current_yul_modules=current['yul_count'],current_yul_closure_targets=current['closure_count'],current_source_union_modules=len(current['modules']),current_additions_read_only=sorted(set(current['yul_modules'])-assigned),original_closure_sources_changed=changed,original_boundary_edges=[dict(importer=i,dependency=d) for i,d in sorted(old_edges)],current_boundary_edges=[dict(importer=i,dependency=d) for i,d in sorted(new_edges)],added_edges=[dict(importer=i,dependency=d) for i,d in sorted(new_edges-old_edges)],removed_edges=[dict(importer=i,dependency=d) for i,d in sorted(old_edges-new_edges)],dependencies=modules,migration_acceptance=False,limitation='Static lexical import census and source hash checks only. No elaborated API, ABI, attribute, semantic, runtime or performance acceptance; directory owners and original frozen constraints remain unchanged.')
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(assigned=len(assigned),old_edges=len(old_edges),current_edges=len(new_edges),external_dependencies=len(dependencies),changed_original_sources=len(changed))))
