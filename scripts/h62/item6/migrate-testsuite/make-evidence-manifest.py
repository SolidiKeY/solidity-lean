#!/usr/bin/env python3
"""Generate a portable hash manifest; bulk H44 evidence remains external."""
import argparse,hashlib,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,default=Path.cwd());ap.add_argument('--evidence-root',type=Path,required=True);ap.add_argument('--archive',type=Path,required=True);ap.add_argument('--descriptor-for',type=Path);a=ap.parse_args()
repo=a.repo.resolve();root=a.evidence_root.resolve()
census=json.loads((root/'census-final.json').read_text())
paths=set(census['closure_sha256'])
for area in ('scripts','tests'):
    for p in (repo/area/'h62/item6/migrate-testsuite').glob('*'):
        if p.suffix in ('.py','.lean','.sh'):paths.add(p.relative_to(repo).as_posix())
def row(path,name):
    with path.open('rb') as stream: digest=hashlib.file_digest(stream,'sha256').hexdigest()
    return {'path':name,'bytes':path.stat().st_size,'sha256':digest}
external=['census-final.json','old-clean-03/census.json','old-clean-03/summary.json','new-clean-01/Solidity.Syntax.Raw.log','new-clean-01/summary.json','new-keysort-01/summary.json','interfaces-old-accepted/interfaces.jsonl','interfaces-old-accepted/summary.json','interfaces-old-dag-01/raw.log','interfaces-old-dag-01/summary.json','public-inventory-old-03/lean.log','public-inventory-old-03/summary.json','resume-01/PublicInventoryStructuredV2.lean','public-api-old-03/inventory.jsonl','public-api-old-03/summary.json','resume-01/python-controls.log','resume-01/reviews.json']
for path,h in census['closure_sha256'].items():
    if row(repo/path,path)['sha256']!=h:raise ValueError('SOURCE_CENSUS_CHANGED: '+path)
full={'schema_version':1,'base':census['base'],'repository_files':[row(repo/p,p) for p in sorted(paths)],'evidence_files':[row(root/p,p) for p in sorted(external)],'archive':row(a.archive,'evidence.tar.gz'),'recorded_evidence_root':str(root),'availability':'External archive/directory must be supplied; no VM path is required for verification. Missing external evidence is pending; present mismatched evidence fails.','boundary':'Old evidence integrity only; all new-toolchain compatibility/parity/final gates remain pending.'}
encoded=json.dumps(full,indent=2)+'\n'
if a.descriptor_for:
    if a.descriptor_for.read_bytes()!=encoded.encode('utf-8'):raise ValueError('DETAIL_MANIFEST_NOT_CURRENT')
    detail=row(a.descriptor_for,a.descriptor_for.name);detail['vm_path']=str(a.descriptor_for.resolve())
    archive=dict(full['archive']);archive['vm_path']=str(a.archive.resolve())
    print(json.dumps({'schema_version':2,'base':census['base'],'detail_manifest':detail,'bulk_archive':archive,'availability':'Supply the pinned detailed manifest and external evidence. VM paths are location hints only; files may be relocated. Missing inputs remain pending.','boundary':full['boundary']},indent=2))
else:
    print(encoded,end='')
