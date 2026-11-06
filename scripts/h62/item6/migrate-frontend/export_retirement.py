#!/usr/bin/env python3
"""Export committed H82 retirement; run with repository writer lock held. No Lean."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[4]
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
BRANCH = 'codex/solidity-h62-6-20261106/migrate-frontend'
EVIDENCE = Path('/workspace/h62-migrate-frontend-evidence')
OUT = EVIDENCE / 'retirement-h82-final'
MANDATORY = 'tests/h62/item6/migrate-frontend/retirement'

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def main():
    assert git('branch', '--show-current').decode().strip() == BRANCH
    assert not git('status', '--porcelain'), 'Commit preservation files first'
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True)
    assert not git('diff', BASE, 'HEAD', '--', 'Solidity/Frontend'), 'Production originals changed'
    head = git('rev-parse', 'HEAD').decode().strip()
    OUT.mkdir(exist_ok=False)
    (OUT / 'cumulative.patch').write_bytes(git('format-patch', '--stdout', BASE + '..' + BRANCH))
    git('bundle', 'create', str(OUT / 'cumulative.bundle'), BASE + '..' + BRANCH)
    result = subprocess.run(['git', '-C', str(ROOT), 'bundle', 'verify', str(OUT / 'cumulative.bundle')], capture_output=True, check=True)
    (OUT / 'bundle-verify.log').write_bytes(result.stdout + result.stderr)
    refs = git('bundle', 'list-heads', str(OUT / 'cumulative.bundle')).decode()
    assert head + ' refs/heads/' + BRANCH in refs
    (OUT / 'bundle-heads.txt').write_text(refs)
    required = OUT / 'mandatory'
    required.mkdir()
    for rel in git('ls-tree', '-r', '--name-only', 'HEAD', '--', MANDATORY).decode().splitlines():
        content = git('show', 'HEAD:' + rel)
        assert (ROOT / rel).read_bytes() == content
        (required / Path(rel).name).write_bytes(content)
    prior = OUT / 'prior-evidence'
    prior.mkdir()
    for name in ['evidence.tar.zst', 'SHA256SUMS', 'handoff.json', 'continuation-queue.json', 'cross-directory-dependencies.json', 'migration-proposal.patch']:
        shutil.copyfile(EVIDENCE / 'handoff' / name, prior / name)
    assert digest(prior / 'SHA256SUMS') == '45490ca1de2c3383be39be5fb706128dd76b54f0ff672b23819715e980334617'
    authenticated = {}
    for line in (prior / 'SHA256SUMS').read_text().splitlines():
        expected, source_path = line.split('  ', 1)
        assert source_path not in authenticated, 'Duplicate prior manifest path'
        authenticated[source_path] = expected
    for payload in sorted(prior.iterdir()):
        if payload.name != 'SHA256SUMS':
            original = str(EVIDENCE / 'handoff' / payload.name)
            assert digest(payload) == authenticated[original], 'Prior payload hash mismatch: ' + original
    queue = json.loads((required / 'open-queue-and-waits.v1.json').read_text())
    report = dict(schema_version=1, status='partial', execution_state='STOPPED', handoff_to=queue['handoff_to'], repository=str(ROOT), branch=BRANCH, base=BASE, head=head, clean=True, production_originals_changed=False, implemented_shims=[], goal_pause=queue['goal_pause'], push=queue['push'], work_queue=queue['work_queue'], backfill_queue=queue['backfill_queue'], waits=queue['waits'], questions=[], validation={'current':'Metadata/JSON, committed scope, unchanged production originals, bundle and checksum verification only; no new Lean run.', 'historical':'See prior-evidence/handoff.json and evidence.tar.zst. Old clean 984/984 passed; new clean failed Source.Ctor target7. Full after timing, generated public API and per-declaration axiom validation remain open.', 'proof_boundary':'Python/OS checks are external; isolated kernel controls do not establish complete Parser equivalence or production acceptance.'}, limitations=['Assignment is incomplete; worker retired by explicit H82.', 'Complete assignment content transcribed; original renderer-byte hash not verified. See prompt-provenance.json.', 'H78 full generated public API/visibility/shim census incomplete; selected271 matches are insufficient.', 'Unapplied Token/Parser definition-body proposals retain applicable owner/trust requirements.', 'Full H68/H69/H80/H81 texts not supplied; obtain authoritative policy.'], mandatory_files={p.name:digest(p) for p in sorted(required.iterdir())})
    (OUT / 'retirement-handoff.json').write_text(json.dumps(report, indent=2) + '\n')
    # Deterministic portable archive, including the complete earlier evidence archive.
    with tarfile.open(OUT / 'retirement-package.tar', 'w', format=tarfile.PAX_FORMAT) as archive:
        for path in sorted(OUT.rglob('*')):
            if path.is_file() and path.name != 'retirement-package.tar':
                info = archive.gettarinfo(str(path), str(path.relative_to(OUT)))
                info.mode = 0o644
                info.pax_headers = {}
                info.uid = info.gid = 0
                info.uname = info.gname = ''
                info.mtime = 0
                with path.open('rb') as stream:
                    archive.addfile(info, stream)
    paths = [p for p in sorted(OUT.rglob('*')) if p.is_file()]
    (OUT / 'SHA256SUMS').write_text(''.join(digest(p) + '  ' + str(p.relative_to(OUT)) + '\n' for p in paths))
    print(json.dumps({'head':head, 'output':str(OUT), 'manifest_sha256':digest(OUT / 'SHA256SUMS')}))

if __name__ == '__main__':
    main()
