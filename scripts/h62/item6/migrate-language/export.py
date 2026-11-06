#!/usr/bin/env python3
"""Export the committed migration checkpoint; never pushes or merges.
Usage: export.py ABSOLUTE_EVIDENCE_DIRECTORY
Bulk artifacts stay outside Git; older checkpoint exports are preserved separately.
"""
import gzip,hashlib,json,pathlib,subprocess,sys,tarfile
root=pathlib.Path(__file__).resolve().parents[4];out=pathlib.Path(sys.argv[1]).resolve()
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
def git(*args): return subprocess.check_output(['git',*args],cwd=root)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not git('status','--porcelain').strip(), 'commit/preserve work before exporting'
head=git('rev-parse','HEAD').decode().strip();branch=git('branch','--show-current').decode().strip()
assert branch=='codex/solidity-h62-6-20261106/migrate-language'
subprocess.run(['git','merge-base','--is-ancestor',base,head],cwd=root,check=True)
census=json.loads((out/'census-final.json').read_text());frozen=json.loads((out/'frozen-comparison.json').read_text())
assert census['inventory_unchanged']
assert not frozen['missing_source_declarations'] and not frozen['changed_source_types']
assert not frozen['missing_source_members'] and not frozen['changed_source_member_types']
assert frozen['source_declared_count']==345 and frozen['source_member_count']==279 and frozen['anonymous_example_count']==44
for r in census['files']:assert digest(root/r['path'])==r['sha256']
response=json.loads((root/'tests/h62/item6/migrate-language/producer-response.json').read_text())
for r in response['patches']:assert digest(pathlib.Path(r['path']))==r['sha256']
(out/'original.patch').write_bytes(git('format-patch','--stdout',base+'..'+head))
bundle=out/'migration.bundle'
if bundle.exists():bundle.unlink()
subprocess.run(['git','bundle','create',str(bundle),base+'..'+branch],cwd=root,check=True)
r=subprocess.run(['git','bundle','verify',str(bundle)],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True)
(out/'bundle-verify.log').write_bytes(r.stdout)
(out/'frozen-sources.sha256').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in census['files']))
transcripts=['frozen-old-final/fixture.log','frozen-new-final/fixture.log','frozen-comparison.json']
(out/'frozen-interfaces.sha256').write_text(''.join(digest(out/p)+'  '+p+'\n' for p in transcripts)+'# source type digest '+frozen['frozen_source_types_sha256']+'\n# constructor/field digest '+frozen['source_members_sha256']+'\n')
timing=json.loads((out/'timing-comparison.json').read_text())
(out/'HANDOFF.md').write_text(f"""# Original-VM migration handoff: root acceptance blocked

Repository: {root}
VM: ccarenv_b64_Y2NhcmVudl9kMTgwY2UzNjkyMGM4MTkxODQxNDVkY2I3NjYwNTc4Mg
Branch: {branch}
Base: {base}
Full committed head: {head}
Reviewed production overlay head: {response['head']}
Continue the SAME existing goal/VM/branch. No goal creation/reset. Coordinator
owns any fresh-thread handoff after completed items.

Local production migration is ready for coordinator retrieval: all8 Language
modules pass on official Lean4.35.0 with no warnings.345 source declarations,
279 explicit constructor/field types and44 anonymous example prefixes preserved;
all original cases compile. No authored axiom/sorry, statement/premise/exclusion,
computation, import or budget change. See committed documentation and exact
live-owner change inventory in producer-response.json.

Owner coordination blocker was resolved by coordinator authorization. Remaining:
B-MIGRATE-HASH: Hash/CollisionBound407/660/680; full run-lean.sh recorded failures
and was interrupted exit-2. B-MIGRATE-SOURCE-CTOR: Source/Ctor641/715 blocks2 direct
consumers. Frontend.Source passes. P8/ForkAgreement also reach Hash. No full gate,
RUNTIME_GATE_PASS or whole-assignment completion.
B-GENERATED-API: root-gate must review6public toCtorIdx removals plus other generated
changes (all listed). B-RSS-REGRESSION:7 modules have increased sampled RSS despite
lower directory peak. No frozen-interface waiver or resource increase implied.
Old clean Language wall {timing['old_language_wall']}s; new {timing['new_language_wall']}s;
delta {timing['wall_delta_percent']:.4f}%, sampled directory RSS delta {timing['rss_delta_percent']:.4f}%.
All module wall times decrease. Exact version/resource/command/exit logs included.

Proof versus test boundaries: typed range/conversion/ABI/storage laws are Lean
kernel checked. Static census/prefix/source reviews are supplementary. No new
solc/EVM differential validation or semantic coverage claim. The structural audit
finds only the existing standard axiom union, but standard dependency graphs drift;
root owns central pin/compatibility acceptance and final toolchain edit.

Full branch patch: {out/'original.patch'} sha256 {digest(out/'original.patch')}
Bundle: {bundle} sha256 {digest(bundle)}
Language-only producer patch: {response['patches'][0]['path']}
SHA256: {response['patches'][0]['sha256']}
FixedPoint-only producer patch: {response['patches'][1]['path']}
SHA256: {response['patches'][1]['sha256']}
Frozen source types SHA256: {frozen['frozen_source_types_sha256']}
Official archive SHA256:7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
Both producer patches apply to fresh pinned-source copies and reproduce expected
bytes (patch-verification.json). Independent finder/skeptic used no Lean/server.
No pushes, merges, master changes, cut-over, freeze or ownership transfer.
""")
relay=out/'hash-relay-evidence.json'
if relay.exists():
    data=json.loads(relay.read_text())
    with (out/'HANDOFF.md').open('a') as f:
        f.write("\nH70 Hash relay update: exact owner patch3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff passes an isolated CollisionBound fixture with no diagnostics. The original repository Hash source remains unchanged. This does not supersede historical full-gate failure or grant full Hash/consumer/root acceptance, owner agreement or any STOP waiver. Full Hash/Syntax.Raw, Source/Ctor and root generated-API/RSS disposition remain pending. See hash-relay-evidence.json and dependency-relay/ for exact source/patch hashes, commands, exits, resource evidence, negative control and independent reviews.\n")
retirement=root/'tests/h62/item6/migrate-language/handoff'
if (retirement/'retirement.json').exists():
    import shutil
    target=out/'retirement';target.mkdir(exist_ok=True)
    for source in retirement.iterdir():
        if source.is_file():shutil.copy2(source,target/source.name)
    handoff=(out/'HANDOFF.md').read_text()
    handoff=handoff.replace('# Original-VM migration handoff: root acceptance blocked','# H82 STOPPED retirement handoff: assignment unfinished',1)
    handoff=handoff.replace('Continue the SAME existing goal/VM/branch. No goal creation/reset. Coordinator\nowns any fresh-thread handoff after completed items.','H82 RETIRED: worker stops after this handoff. No automatic implementation continuation.\nHandoff_to solidity-h62-6-20261106/migrate-root-gate; successor integrates final head.\nExisting goal PAUSED requested, backend update unavailable: no callable PAUSED API.\nNo goal completion/reset/replacement; preserve original VM/branch/evidence.')
    handoff+='\nFull original assignment, original goal context, unabridged work/backfill queue, exact scope manifest, H82 orders, all open-item/wait dispositions and prompt provenance are committed under tests/h62/item6/migrate-language/handoff/ and copied into retirement/. See retirement/SHA256SUMS for each actual file digest. Historical launcher rendered-envelope digest is not claimed equal to the captured full thread-text digest. H71 permission unavailable: no push attempted. All prior evidence statements are historical validation boundaries, not instructions to resume this retired worker.\n'
    (out/'HANDOFF.md').write_text(handoff)
excluded={'build','cache','__pycache__','serial-sysroot','shims','previous-blocked','patch-verification'}
files=sorted(p for p in out.rglob('*') if p.is_file() and not p.is_symlink() and not excluded.intersection(p.relative_to(out).parts) and p not in {out/'SHA256SUMS',out/'evidence.tar.gz'})
with (out/'evidence.tar.gz').open('wb') as f,gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as gz,tarfile.open(fileobj=gz,mode='w') as tar:
    for p in files:
        info=tar.gettarinfo(str(p),arcname=str(p.relative_to(out)))
        info.uid=info.gid=info.mtime=0;info.uname=info.gname='';info.mode=0o644
        with p.open('rb') as source:tar.addfile(info,source)
files.append(out/'evidence.tar.gz')
(out/'SHA256SUMS').write_text(''.join(digest(p)+'  '+str(p.relative_to(out))+'\n' for p in sorted(files)))
print(json.dumps(dict(head=head,patch_sha256=digest(out/'original.patch'),bundle_sha256=digest(bundle),archive_sha256=digest(out/'evidence.tar.gz'),manifest_sha256=digest(out/'SHA256SUMS')),indent=2))
