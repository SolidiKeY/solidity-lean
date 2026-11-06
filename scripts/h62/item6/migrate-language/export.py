#!/usr/bin/env python3
"""Export this isolated committed checkpoint; never pushes or merges.
Run from the worktree after committing, with absolute evidence directory argument.
Bulk evidence and hashes stay outside Git. Existing export names are refreshed.
"""
import gzip, hashlib, json, pathlib, subprocess, sys, tarfile
root=pathlib.Path(__file__).resolve().parents[4]
out=pathlib.Path(sys.argv[1]).resolve()
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
def git(*args): return subprocess.check_output(['git',*args],cwd=root)
assert not git('status','--porcelain').strip(), 'commit/preserve work before exporting'
head=git('rev-parse','HEAD').decode().strip()
branch=git('branch','--show-current').decode().strip()
assert branch=='codex/solidity-h62-6-20261106/migrate-language'
subprocess.run(['git','merge-base','--is-ancestor',base,head],cwd=root,check=True)
(out/'original.patch').write_bytes(git('format-patch','--stdout',base+'..'+head))
bundle=out/'migration.bundle'
if bundle.exists(): bundle.unlink()
subprocess.run(['git','bundle','create',str(bundle),base+'..'+head],cwd=root,check=True)
r=subprocess.run(['git','bundle','verify',str(bundle)],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True)
(out/'bundle-verify.log').write_bytes(r.stdout)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
census=json.loads((out/'census-final.json').read_text())
assert census['inventory_unchanged'] and all(r['unchanged'] for r in census['files'])
(out/'frozen-sources.sha256').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in census['files']))
(out/'frozen-interfaces.sha256').write_text(digest(out/'interface-old/fixture.log')+'  interface-old/fixture.log  # BASELINE ONLY, new comparison pending\n')
(out/'HANDOFF.md').write_text(f"""# Blocked original-VM handoff

Repository: {root}
Original VM: ccarenv_b64_Y2NhcmVudl9kMTgwY2UzNjkyMGM4MTkxODQxNDVkY2I3NjYwNTc4Mg
Branch: {branch}
Base: {base}
Committed head: {head}
Status: blocked; full persistent assignment unfinished. Continue the SAME goal/VM;
coordinator owns any fresh-thread handoff. Do not create/reset a goal.

Read committed docs/feature-work/h62-6-migrate-language.md for all commands,
versions, resource bounds, proof boundaries, independent review fixes and queues.
OWNER-EXACT-FILE-ACK: required relay.sh absent; coordinator exact-file acknowledgement
pending before any production migration edits. Existing eight sources unchanged.
Old clean 8/8 pass:45.30031436s,879906816B peak sampled aggregate RSS.
New KeySort + catalogs pass, FixedPoint fails. Six fixed-point modules unaccepted.
No overall timing delta, no RUNTIME_GATE_PASS. Full affected/default-target gate,
production repairs, new interfaces/axiom comparison, clean timings and final
acceptance/reviews remain. No theorem weakening, axiom or authored sorry added.

Patch is additive tooling/tests/docs ONLY; it is not a production migration patch.
Patch: {out/'original.patch'} sha256 {digest(out/'original.patch')}
Bundle: {bundle} sha256 {digest(bundle)}
Baseline interfaces sha256 {digest(out/'interface-old/fixture.log')}
Toolchain archive sha256 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
All source hashes and final evidence checksums are adjacent. Bulk build directories
are excluded from the portable evidence archive; full local logs remain available.
No pushes, merges, master changes, cut-over or live-owner transfers.
""")
excluded={'build','cache','__pycache__'}
export_names={'SHA256SUMS','evidence.tar.gz'}
files=sorted(p for p in out.rglob('*') if p.is_file() and not excluded.intersection(p.relative_to(out).parts) and p.name not in export_names)
with (out/'evidence.tar.gz').open('wb') as f, gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as gz, tarfile.open(fileobj=gz,mode='w') as tar:
    for p in files:
        info=tar.gettarinfo(str(p),arcname=str(p.relative_to(out)))
        info.uid=info.gid=info.mtime=0; info.uname=info.gname=''; info.mode=0o644
        with p.open('rb') as source: tar.addfile(info,source)
files.append(out/'evidence.tar.gz')
(out/'SHA256SUMS').write_text(''.join(digest(p)+'  '+str(p.relative_to(out))+'\n' for p in sorted(files)))
print(json.dumps(dict(head=head,patch_sha256=digest(out/'original.patch'),bundle_sha256=digest(bundle),archive_sha256=digest(out/'evidence.tar.gz'),manifest_sha256=digest(out/'SHA256SUMS')),indent=2))
