"""Prepare and verify an H41 pickup packet; never sends data or edits cache mappings."""
import hashlib, json, os, pathlib, subprocess, sys, tarfile
repo = pathlib.Path(__file__).resolve().parents[3]
cache = pathlib.Path(os.environ['LAKE_CACHE_DIR'])
out = pathlib.Path(sys.argv[1]).resolve()
out.mkdir(exist_ok=False)
art = cache/'artifacts'
names = {}
for p in art.iterdir():
    names.setdefault(p.name.split('.', 1)[0], []).append(p.name)
mappings = {}
for line in (cache/'inputs/solidity-lean.jsonl').read_text().splitlines():
    try: mappings[json.loads(line)[0]] = line
    except (ValueError, IndexError): pass
selected = {}; members = set(); omitted = 0
for trace in (repo/'.lake/build').rglob('*.trace'):
    try: data = json.loads(trace.read_text())
    except (ValueError, OSError): continue
    key = data.get('depHash'); outputs = data.get('outputs')
    if key not in mappings or outputs is None:
        omitted += 1; continue
    assert json.loads(mappings[key])[1] == outputs, f"trace/mapping mismatch: {trace}"
    hashes = [outputs] if isinstance(outputs, str) else [h for v in outputs.values() for h in (v if isinstance(v, list) else [v])]
    if not hashes or any(str(h) not in names for h in hashes):
        omitted += 1; continue
    selected[key] = mappings[key]
    members.update(n for h in hashes for n in names[str(h)])
assert members
manifest = {n: {'size': (art/n).stat().st_size, 'sha256': hashlib.file_digest((art/n).open('rb'), 'sha256').hexdigest()} for n in sorted(members)}
(out/'artifacts.json').write_text(json.dumps(manifest, indent=2)+'\n')
(out/'inputs.solidity-lean.jsonl').write_text('\n'.join(selected.values())+'\n')
(out/'members.txt').write_text('\n'.join(sorted(members))+'\n')
head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
(out/'HEAD').write_text(head+'\n')
archive = out/'cache.tar.zst'
with archive.open('wb') as f:
    tar = subprocess.Popen(['tar', '-C', str(art), '-cf', '-', '-T', str(out/'members.txt')], stdout=subprocess.PIPE)
    z = subprocess.Popen(['zstd', '-T1', '-3', '-q'], stdin=tar.stdout, stdout=f)
    tar.stdout.close()
    assert z.wait() == 0
    assert tar.wait() == 0
# Read every archived byte back, with no extraction or path traversal.
p = subprocess.Popen(['zstd', '-dc', str(archive)], stdout=subprocess.PIPE)
seen = set()
with tarfile.open(fileobj=p.stdout, mode='r|') as stream:
    for item in stream:
        assert item.isfile() and item.name in manifest and item.name not in seen
        expected = manifest[item.name]
        assert item.size == expected['size']
        assert hashlib.file_digest(stream.extractfile(item), 'sha256').hexdigest() == expected['sha256']
        seen.add(item.name)
p.stdout.close()
assert p.wait() == 0 and seen == set(manifest)
receipt = {'status': 'coordinator-pending', 'head': head, 'archive': str(archive), 'sha256': hashlib.file_digest(archive.open('rb'), 'sha256').hexdigest(), 'bytes': archive.stat().st_size, 'artifacts': len(members), 'mappings': len(selected), 'omittedTraces': omitted, 'archiveReadbackVerified': True, 'scope': 'Present cache mappings and trace outputs only; not a full-tree build/freshness claim. No remote shipment or mapping mutation.'}
(out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
