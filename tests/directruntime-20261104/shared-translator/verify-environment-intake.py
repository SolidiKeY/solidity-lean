"""Guard historical environment payload intake against freshness overclaims.

Authenticate sealed indexes and all payload bytes without extraction, installation,
wrapper/binary execution, timing reruns or source-preservation claims.
"""
import argparse, collections, hashlib, importlib.util, json, re, tarfile
from pathlib import Path
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sealed_intake', HERE / 'verify-sourcebuild-intake.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
require = helper.require
sha = helper.digest
PINS = {
 'native-browser-wrapper-handoff-5a21.json': 'a53f2f972de3748860f20545fd0f6ffdef3d714d5fbb97e3d3de73e5dca6b365',
 'native-browser-wrapper-index-5a21.json': '643f9d637d9f12ffd74fe5857a17becaefe0c30755071c6d3fe98de4b843e617',
 'native-browser-e7ef/evidence.tar.gz': 'c3c9ce432635b63557700dc3bb01d217f266943a9bf908e964944e5735d7e705',
 'native-browser-e7ef/runtime-artifacts.tar.gz': 'b0f6775171d94000d1c4c944d2b4688b42fc39312dff6c2ede8824f19ceaa179',
 'native-browser-e7ef/incremental-cache.tar.gz': '0c3f22d411897b4f0822fa8b4f11b8ea4ec77e1bcd8cedc21fdbff4fabf85aee',
 'native-browser-e7ef/evidence-files.json': '8a9c1aa9542561b541aeeccbae0ae2f9625b1e77a13754a5aa717b858023158b',
 'native-browser-e7ef/runtime-files.json': '4e7ffa48711a3bf7ffa87a2f3c4cf6584016d2eab22d913db65312d7c71cbaa2',
 'native-browser-e7ef/cache-files.json': '1d5d390f4e035f94efcd4981115eb3ffc3ddd9c1b7fc002ee3d043a1d7cc39c9'}
SOURCE = '4d7285b80e89741e9da8cb49ce7ab8b62a828a72'


def indexed(directory, archive, index):
    rawindex = (directory / index).read_bytes()
    document = json.loads(rawindex)
    rows = document if isinstance(document, list) else document['files']
    expected = {r['path']: r for r in rows}
    require(len(expected) == len(rows) and index not in expected, 'duplicate/index payload path')
    data = {}
    with tarfile.open(directory / archive, 'r:gz') as tar:
        entries = helper.members(tar)
        require(set(entries) == set(expected) | {index}, 'sealed archive member set')
        require(tar.extractfile(index).read() == rawindex, 'embedded index differs')
        for name, row in expected.items():
            raw = tar.extractfile(name).read()
            require(len(raw) == row['bytes'] and sha(raw) == row['sha256'], 'payload hash/size: ' + name)
            data[name] = raw
    return data, {'payloads': len(rows), 'regularMembersIncludingIndex': len(rows) + 1,
                  'payloadBytes': sum(r['bytes'] for r in rows)}


def verify(inbox):
    for name, pin in PINS.items():
        require(sha((inbox / name).read_bytes()) == pin, 'outer pin: ' + name)
    wrapper = json.loads((inbox / 'native-browser-wrapper-index-5a21.json').read_text())
    require(wrapper['sourceBuildHead'] == SOURCE, 'wrapper source-build boundary')
    directory = inbox / 'native-browser-e7ef'
    evidence, es = indexed(directory, 'evidence.tar.gz', 'evidence-files.json')
    runtime, rs = indexed(directory, 'runtime-artifacts.tar.gz', 'runtime-files.json')
    cache, cs = indexed(directory, 'incremental-cache.tar.gz', 'cache-files.json')
    wrapperNames = [r['archiveMember'] for r in wrapper['wrappers']]
    require(len(set(wrapperNames)) == len(wrapperNames), 'duplicate wrapper binding')
    for row in wrapper['wrappers']:
        require(row['archiveMember'] in evidence, 'missing historical wrapper')
        raw = evidence[row['archiveMember']]
        require(len(raw) == row['bytes'] and sha(raw) == row['sha256'], 'historical wrapper hash/size')
    native = json.loads(runtime['native/build.json'])
    wasm = json.loads(runtime['direct/build.json'])
    require(native['sourceFiles'] == wasm['sourceFiles'] and len(native['sourceFiles']) ==
            len({r['module'] for r in native['sourceFiles']}) == 343, 'build source-array consistency')
    for name, pin in [('native/direct-check', native['executable']),
                      ('direct/direct.wasm', wasm['wasm']), ('direct/direct.js', wasm['javascript'])]:
        require(sha(runtime[name]) == pin, 'build binary binding: ' + name)
    cacheindex = json.loads((directory / 'cache-files.json').read_text())
    require(cacheindex['sourceBuildHead'] == SOURCE, 'cache source-build boundary')
    controls = []
    for modality in ['box', 'diamond']:
        d = json.loads(evidence['evidence/environment-' + modality + '-controls/control-inventory-with-guard.json'])
        require(not d['errors'] and d['inventoryCompleted'], 'unfinished environment inventory')
        require(d['freshness']['native']['binarySha256'] == native['executable'] and
                d['freshness']['wasm']['binarySha256'] == wasm['wasm'], 'inventory binary binding')
        wanted = d['names']
        require(len(set(wanted)) == len(wanted), 'duplicate selected function')
        require(d['positiveHarnessGuard']['name'] not in wanted and
                len(d['native']) == len(wanted) + 1 == d['expectedRequestsPerBackend'] and
                d['expectedControlRequests'] == len(wanted), 'selected plus mandatory guard denominator')
        counts = collections.Counter()
        names = []
        require(len(d['native']) == len(d['browser']), 'backend request count')
        for n, w in zip(d['native'], d['browser'], strict=True):
            require(n['name'] == w['name'] and n['wireSha256'] == w['wireSha256'], 'request parity')
            require(n['reply']['results'] == w['reply']['results'], 'core result parity')
            require(w['boot']['build'] == wasm['wasm'], 'browser boot binding')
            if n['name'] not in wanted:
                require(n['name'] == d['positiveHarnessGuard']['name'] and
                        [r['status'] for r in n['reply']['results']] == ['proved'], 'positive harness guard')
                continue
            require(len(n['reply']['results']) == 1, 'selected result denominator')
            row = n['reply']['results'][0]
            require(row['function'] == n['name'] and row['tag'] == modality, 'result identity/modality')
            names.append(n['name']); counts[row['status']] += 1
        require(len(names) == len(wanted) and set(names) == set(wanted), 'selected request coverage')
        controls.append({'modality': modality, 'cases': len(names), 'perBackend': dict(counts),
                         'coreResultParity': True})
    negatives = json.loads(evidence['evidence/negative-controls/browser-control-completion.json'])
    require(negatives['binarySha256'] == wasm['wasm'], 'stack-failure binary binding')
    failures = negatives['failures']
    require(not negatives['passed'] and any(f['record']['name'] == 'invariantCountsToBound'
            for f in failures), 'known failure disappeared')
    stackFailure = next(f['record'] for f in failures if f['record']['name'] == 'invariantCountsToBound')
    workerError = stackFailure['reply']['workerError']
    require(workerError['message'] == 'Maximum call stack size exceeded', 'retained stack-error message')
    frameIndices = [int(x) for x in re.findall(r'wasm-function\[([0-9]+)\]', workerError['stack'])]
    require(bool(frameIndices), 'retained stack frames missing')
    gates = []
    for name, raw in evidence.items():
        if name.endswith('gate.json'):
            gate = json.loads(raw)
            gates.append({'path': name, 'exit': gate.get('exitCode', gate.get('exit'))})
    return {'guardedRegression': __doc__.splitlines()[0], 'inputs': PINS,
            'reportedSourceBuildHead': SOURCE, 'evidence': es, 'runtime': rs, 'cache': cs,
            'historicalWrappersBoundToEvidence': len(wrapperNames),
            'recordedSourceModules': len(native['sourceFiles']), 'environmentControls': controls,
            'gateReceipts': gates, 'retainedFailureNames': [f['record']['name'] for f in failures],
            'retainedStack': {'message': workerError['message'], 'functionIndices': frameIndices,
                              'symbolization': 'Not mapped; historical6ae symbols are not a map for this5a5be8 binary.'},
            'nativeSha256': native['executable'], 'wasmSha256': wasm['wasm'],
            'extraction': False, 'execution': False, 'cacheInstalled': False,
            'gitSourceIdentityVerified': False,
            'boundary': 'Historical sealed payload/index/build-manifest consistency and saved request/result parity only. No current reader qualification, Git source verification, compiler/source transport, universal native correctness, performance STOP release or runtime gate acceptance. Original producer d8a141a7 evidence remains a separate undelivered archive.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--inbox', type=Path, default=Path('/workspace/h62-coordinator-inputs'))
    args = parser.parse_args()
    print(json.dumps(verify(args.inbox), indent=2))
