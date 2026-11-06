#!/usr/bin/env python3
"""Export the committed preparation bundle and UNAPPLIED proposals; no publishing."""
import argparse
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess

BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
BRANCH='codex/solidity-h62-6-20261106/migrate-frontend'

def sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path.cwd());ap.add_argument('--evidence',type=Path,default=Path('/workspace/h62-migrate-frontend-evidence'));a=ap.parse_args()
    root=a.root.resolve();e=a.evidence.resolve();out=e/'handoff';out.mkdir(exist_ok=True)
    lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    def git(*args):return subprocess.check_output(['git',*args],cwd=root)
    head=git('rev-parse','HEAD').decode().strip()
    if git('branch','--show-current').decode().strip()!=BRANCH:raise SystemExit('Wrong branch')
    subprocess.run(['git','merge-base','--is-ancestor',BASE,head],cwd=root,check=True)
    if git('status','--porcelain'):raise SystemExit('Commit owned changes before exporting')
    changed=git('diff','--name-only',BASE,head).decode().splitlines()
    allowed=('scripts/h62/item6/migrate-frontend/','tests/h62/item6/migrate-frontend/')
    if any(not (p.startswith(allowed) or p=='docs/feature-work/h62-6-migrate-frontend.md') for p in changed):raise SystemExit('Unexpected changed path')
    # Keep original production source unchanged; candidate source is separate.
    if git('diff',BASE,head,'--','Solidity/Frontend/'):raise SystemExit('Original Frontend source unexpectedly edited')
    patch=out/'branch-preparation.patch';patch.write_bytes(git('format-patch','--stdout',BASE+'..'+head))
    bundle=out/'branch-preparation.bundle'
    if bundle.exists():bundle.unlink()
    subprocess.run(['git','bundle','create',str(bundle),BASE+'..'+BRANCH],cwd=root,check=True)
    with (out/'bundle-verify.log').open('w') as log:subprocess.run(['git','bundle','verify',str(bundle)],cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
    advertised=git('bundle','list-heads',str(bundle)).decode().splitlines()
    if not any(line.split()[0]==head for line in advertised):raise SystemExit('Bundle tip mismatch')
    candidates=[e/'token-overlay-v5/token-v435.patch',e/'parser-overlay-v3/parser-v435.patch']
    proposal=out/'migration-proposal.patch';proposal.write_bytes(b''.join(p.read_bytes() for p in candidates))
    subprocess.run(['git','apply','--check',str(proposal)],cwd=root,check=True)
    baseline=json.loads((e/'old-clean-serial/measurement.json').read_text());new=json.loads((e/'new-clean-serial/measurement.json').read_text())
    handoff={'batch':'solidity-h62-6-20261106','slug':'migrate-frontend','status':'blocked','branch':BRANCH,'base':BASE,'head':head,'repository':str(root),'original_environment':json.loads((e/'setup.json').read_text())['environment_id'],'existing_goal':'Full original assignment unfinished; continue same goal/VM/branch. No goal reset or replacement.','checkpoints':[{'name':'1 census and clean old baseline','status':'done'},{'name':'2 pinned new toolchain and adaptation','status':'blocked'},{'name':'3 complete new validation and clean performance comparison','status':'blocked'},{'name':'4 final migration overlay/root-gate handoff','status':'partial'}],'old_baseline':{'modules':len(baseline['results']),'frontend_modules':490,'wall_seconds':baseline['wall_seconds'],'peak_group_rss_bytes_sampled':baseline['peak_group_rss_bytes_sampled']},'new_attempt':{'rows':len(new['results']),'status':new['status'],'blocking_module':'Solidity.Source.Ctor','wall_delta_percent':None},'frozen_original_files_changed':0,'candidate_declared_types_checked':271,'new_production_declarations':0,'isolated_control_theorems':12,'new_axiom_declarations':0,'sorry_added':0,'native_decide_added':0,'heartbeats_raised':False,'full_runtime_gate':'pending; no pass claimed','owner_requests':str(root/'tests/h62/item6/migrate-frontend/owner-requests.json'),'handoff_document':str(root/'docs/feature-work/h62-6-migrate-frontend.md'),'cross_directory_report':str(out/'cross-directory-dependencies.json'),'continuation_queue':str(out/'continuation-queue.json'),'proof_test_boundary':'Old clean Lean build and isolated kernel controls passed. Python/OS/static/hash tests are external checks. Universal Parser equivalence, per-declaration axiom approval, whole new directory/root acceptance and performance remain unproved/unvalidated.','reviews':str(e/'reviews-tooling.json'),'static_gate_results':str(e/'static-gates/results.json'),'limitations':['Source.Ctor owner migration required at unchanged statement/budget','Original Token/Parser edits need exact-file producer coordination; proposals are unapplied','ascii and66Parser declaration standard-axiom changes pending root allowlist review','244Ctor-dependent and246otherFrontend targets not completely validated on new toolchain','Tokenv5 whole generator fails at original Parser smoke; isolated Token commands pass; Parsercandidate pipeline remedies it only in fixture artifacts','Full old/new frozen-interface comparison and clean after timing pending','Baseline doc-path check fails on unchanged outside-scope optional-Mathlib reference; lane document has no finding','Fresh-thread handoff due after5bounded reviewed items; coordinator owns continuation'],'questions':[],'artifacts':{'original_patch':str(proposal),'original_patch_status':'UNAPPLIED partial migration proposal, not an accepted completed overlay','branch_patch':str(patch),'branch_bundle':str(bundle),'handoff':str(out/'handoff.json'),'evidence':str(e),'archive':str(out/'evidence.tar.zst'),'checksums':str(out/'SHA256SUMS')}}
    (out/'handoff.json').write_text(json.dumps(handoff,indent=2)+'\n')
    # Package evidence, excluding derived build trees and installed toolchains.
    # Full on-VM outputs remain available and are checksum-manifested below.
    archive=out/'evidence.tar.zst'
    selected=[]
    for path in sorted(e.rglob('*')):
        if not path.is_file():continue
        rel=path.relative_to(e)
        if rel.parts[0] in ('toolchains','handoff') or 'build' in rel.parts or rel.parts[0] in ('old','new'):continue
        selected.append(str(rel))
    listing=out/'archive-files.txt';listing.write_text('\n'.join(selected)+'\n')
    subprocess.run(['tar','--sort=name','--mtime=@0','--owner=0','--group=0','--numeric-owner','--zstd','-cf',str(archive),'-C',str(e),'-T',str(listing)],check=True)
    manifest=out/'SHA256SUMS';rows=[]
    for path in sorted(e.rglob('*')):
        if not path.is_file() or path==manifest:continue
        rel=path.relative_to(e)
        if rel.parts[0]=='toolchains' and path.name!='lean-4.35.0-linux.tar.zst':continue
        rows.append((str(path),sha(path)))
    old_archive=Path('/workspace/.setup/tools/lean-4.24.0-linux.tar.zst')
    rows.append((str(old_archive),sha(old_archive)))
    manifest.write_text(''.join(f'{digest}  {name}\n' for name,digest in sorted(rows)))
    print(json.dumps({'head':head,'migration_proposal_sha256':sha(proposal),'bundle_sha256':sha(bundle),'handoff_sha256':sha(out/'handoff.json'),'archive_sha256':sha(archive),'checksums_sha256':sha(manifest),'checksummed_files':len(rows)}))
if __name__=='__main__':main()
