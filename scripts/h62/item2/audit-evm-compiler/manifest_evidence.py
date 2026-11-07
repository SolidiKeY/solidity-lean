#!/usr/bin/env python3
"""Create the committed relative manifest after the audit gates/reviews finish.
This records observed artifact bytes; it does not certify or re-run proofs.
"""
import argparse,gzip,hashlib,io,json,pathlib,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[4]
p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);p.add_argument('--output',required=True);p.add_argument('--archive',required=True);p.add_argument('--supplement',help='JSON with additional relative source/artifact paths and scope');p.add_argument('--index-output',default=str(ROOT/'tests/h62/item2/audit-evm-compiler/evidence-manifest.json')); a=p.parse_args()
e=pathlib.Path(a.evidence).resolve()
full=pathlib.Path(a.output).resolve();archive=pathlib.Path(a.archive).resolve()
if full.is_relative_to(ROOT) or archive.is_relative_to(ROOT):raise ValueError('bulk outputs must be outside the repository')
sources=['scripts/h62/item2/audit-evm-compiler/'+n for n in ['Closed.lean','closed_census.py','reconcile.py','verify_evidence.py','manifest_evidence.py','bounded.py','census.py','Inspect.lean']]+['tests/h62/item2/audit-evm-compiler/'+n for n in ['JointWitness.lean','coverage.json','check_evidence.py','handoff/original-rendered-prompt.md']]+['docs/module-map/evm-compiler.md','lean-toolchain']
artifacts=['versions.json','keysort.json','keysort.log','seed-census.json','source-census.json','kernel.jsonl','statement-census.json','ownership-snapshot.json','closed-checks.jsonl','closed-coverage.json','closed-summary.json','promotion-summary.json','telescope-timing.json','before-telescope.json','tool-final.json','tool-final.log','evidence-controls.log','duplicate-ledger-control.log','final-gates.json','integrity.json','reviews.md']
artifacts+=sorted(p.name for p in e.glob('closed-Solidity*') if p.suffix in ['.json','.log'])
artifacts+=sorted(p.name for p in e.glob('final-*') if p.suffix in ['.json','.log'])
census=json.loads((e/'source-census.json').read_text())
sources += [m if m.startswith('Bridge/') else 'Solidity/'+m for m in census['modules']]
sources += ['tests/h62/item2/audit-evm-compiler/'+n+'.lean' for n in ['LayoutAudit','SuccessAudit','HeadlineAudit','JointImpossible','JointWitness','IntentionalAudit','OpcodeAudit','JumpdestAudit']]
artifacts += [g['evidence'] for g in json.loads((e/'final-gates.json').read_text())['gates']]
supplement=json.loads(pathlib.Path(a.supplement).read_text()) if a.supplement else {}
sources+=supplement.get('sources',[]);artifacts+=supplement.get('artifacts',[])
for item in sources+artifacts:
    if pathlib.PurePosixPath(item).is_absolute() or '..' in pathlib.PurePosixPath(item).parts:raise ValueError('relative paths required')
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
summary=json.loads((e/'closed-summary.json').read_text());promoted=json.loads((e/'promotion-summary.json').read_text())
if summary['failed_modules'] or summary['checked_count']!=summary['candidate_count']:raise ValueError('closed batch not fully checked')
m=dict(schema_version=1,archive_root='continuation-2',frozen_base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4',toolchain=(ROOT/'lean-toolchain').read_text().strip(),scope=supplement.get('scope','Closed-input equality classification; hashes are byte integrity, not proof replay or compiler totality.'),sources=[dict(path=s,sha256=sha(ROOT/s)) for s in sorted(set(sources))],artifacts=[dict(path=s,sha256=sha(e/s)) for s in sorted(set(artifacts))],counts=promoted)
full.write_text(json.dumps(m,indent=2)+'\n')
with archive.open('wb') as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=6) as zipped:
        with tarfile.open(fileobj=zipped,mode='w',format=tarfile.PAX_FORMAT) as bundle:
            def add_data(path,name):
                data=path.read_bytes();entry=tarfile.TarInfo(name)
                entry.size=len(data);entry.mtime=0;entry.mode=0o644
                entry.uid=entry.gid=0;entry.uname=entry.gname=''
                bundle.addfile(entry,io.BytesIO(data))
            for item in m['artifacts']:add_data(e/item['path'],m['archive_root']+'/'+item['path'])
            add_data(full,m['archive_root']+'/evidence-manifest.json')
index=dict(schema_version=2,frozen_base=m['frozen_base'],full_manifest=dict(path=str(full),size_bytes=full.stat().st_size,sha256=sha(full),archive_member=m['archive_root']+'/evidence-manifest.json'),archive=dict(path=str(archive),size_bytes=archive.stat().st_size,sha256=sha(archive)))
pathlib.Path(a.index_output).write_text(json.dumps(index,indent=2)+'\n')
print(json.dumps(dict(sources=len(m['sources']),artifacts=len(m['artifacts']),full_manifest=str(full),archive=str(archive))))
