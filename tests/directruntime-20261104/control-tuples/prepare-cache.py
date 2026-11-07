#!/usr/bin/env python3
"""Prepare a verified owned-module cache archive; never assert delivery."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

repo = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent / 'evidence'
cache = Path('/workspace/.setup/cache/lake')
artifacts = cache / 'artifacts'
parser = argparse.ArgumentParser(description="H41: prepare a verified pack for coordinator retrieval; never run worker shipping")
parser.add_argument('--validation', required=True)
parser.add_argument('--archive', required=True)
parser.add_argument('--receipt', required=True)
args = parser.parse_args()
validation = (repo / args.validation).resolve()
archive = (repo / args.archive).resolve()
receipt_path = (repo / args.receipt).resolve()
assert archive.parent == evidence.resolve() and receipt_path.parent == evidence.resolve()
assert archive != receipt_path, 'archive and receipt must be distinct paths'
assert not archive.exists() and not receipt_path.exists(), 'preserve prior packs/receipts; choose new paths'
gate = json.loads(validation.read_text())
assert gate['exit'] == 0 and not gate['resource_stop']
for name, digest in gate['source_sha256'].items():
    assert hashlib.sha256((repo / name).read_bytes()).hexdigest() == digest, name
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
assert gate['head'] == head, 'validate this source head before cache preparation'
mappings = {}
for line in (cache / 'inputs/solidity-lean.jsonl').read_text().splitlines():
    key, value = json.loads(line)
    mappings.setdefault(str(key), []).append((value, line))
files = {}
selected_lines = []
modules = []
for module in ['Adapter', 'AdmissionControls', 'IntrinsicControls']:
    stem = 'Solidity/Frontend/ExecutableAst/ControlTuple/' + module
    trace_path = repo / ('.lake/build/lib/lean/' + stem + '.trace')
    trace = json.loads(trace_path.read_text())
    key = str(trace['depHash'])
    matches = [line for value, line in mappings.get(key, []) if value == trace['outputs']]
    assert matches, 'no exact cache mapping for ' + module
    selected_lines.append(matches[-1])
    hashes = [str(x) for value in trace['outputs'].values()
              for x in (value if isinstance(value, list) else [value])]
    names = []
    for digest in hashes:
        found = sorted(artifacts.glob(digest + '.*'))
        assert found, 'missing output ' + digest
        for artifact in found:
            assert artifact.is_file() and artifact.resolve().parent == artifacts.resolve()
            files['artifacts/' + artifact.name] = artifact.read_bytes()
            names.append(artifact.name)
    files['traces/' + module + '.trace'] = trace_path.read_bytes()
    source = repo / (stem + '.lean')
    modules.append({'module': stem.replace('/', '.'), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                    'input_hash': key, 'outputs': trace['outputs'], 'artifact_names': names})
files['inputs/solidity-lean.jsonl'] = ('\n'.join(selected_lines) + '\n').encode()
metadata = {'status': 'coordinator-pending', 'source_head': head, 'package': 'solidity-lean',
            'toolchain': (repo / 'lean-toolchain').read_text().strip(), 'modules': modules,
            'gate_evidence': str(validation),
            'restore_rule': 'Coordinator must verify hashes, preserve existing artifacts and append exact input lines under Lake CacheMap lock; no worker installation or delivery performed.'}
files['metadata.json'] = (json.dumps(metadata, indent=2) + '\n').encode()
sums = ''.join(hashlib.sha256(value).hexdigest() + '  ' + name + '\n' for name, value in sorted(files.items()))
files['SHA256SUMS'] = sums.encode()
with archive.open('xb') as output:
    compressor = subprocess.Popen(['zstd', '-T1', '-3', '-q', '-c'], stdin=subprocess.PIPE, stdout=output)
    with tarfile.open(fileobj=compressor.stdin, mode='w|') as tar:
        for name, value in sorted(files.items()):
            entry = tarfile.TarInfo(name)
            entry.size = len(value)
            entry.mode = 0o644
            entry.mtime = 0
            tar.addfile(entry, io.BytesIO(value))
    compressor.stdin.close()
    assert compressor.wait() == 0, 'compression failed'
# Read every archived member back without extracting into any active cache.
decoder = subprocess.Popen(['zstd', '-q', '-d', '-c', str(archive)], stdout=subprocess.PIPE)
seen = set()
with tarfile.open(fileobj=decoder.stdout, mode='r|') as tar:
    for entry in tar:
        assert entry.isfile() and entry.name in files and entry.name not in seen
        value = tar.extractfile(entry).read()
        assert value == files[entry.name], entry.name
        seen.add(entry.name)
assert decoder.wait() == 0 and seen == set(files)
receipt = {'policy': 'H41', 'status': 'coordinator-pending', 'coordinator_pull_reported': False, 'delivery_complete': False, 'destination_receipt': None,
           'source_head': head, 'validation': str(validation),
           'archive': str(archive), 'archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
           'archive_bytes': archive.stat().st_size, 'artifact_count': sum(n.startswith('artifacts/') for n in files),
           'mapping_count': len(selected_lines), 'members_verified': len(seen), 'dependency_closure_included': False,
           'worker_shipping_performed': False, 'worker_must_not_run_ship_cache': True}
with receipt_path.open('x') as output:
    output.write(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
