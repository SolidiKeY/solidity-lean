"""Guard against treating a delivered handoff's metadata as inspected runtime payloads.
Checks pinned address16 metadata and Git source bytes only. Never executes or
extracts delivered code, opens its archives, or reruns stopped benchmarks.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[3]
HEAD = 'a14d56c9a8d45f5b085c2a5f3f15882916779716'
SOURCE = '0eb39db1dba7f81e4d8d0b4756ab50b87d4dcd6d'
HANDOFF_SHA = '5bdf0e65c060c2570d59e81e2368744741c3e9972e84edf0269df95851b98d9e'
MANIFEST = 'tests/directruntime-20261104/native-browser/address/post-merge-manifest.json'
MANIFEST_SHA = '0ef980d6a84b1a6b1cdf4fb5b3cfb1885534d1b1083a7b01b92fe043e852d8ba'
DEFAULT = Path('/workspace/h62-coordinator-inputs/router-20261107T055306Z') / (HANDOFF_SHA + '.ticket')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git_bytes(head, path):
    return subprocess.check_output(['git', 'show', head + ':' + path], cwd=ROOT)


def check_metadata(handoff, manifest):
    """Check report consistency, without promoting declared observations to evidence."""
    require(handoff['head'] == HEAD and handoff['sourceBuildHead'] == SOURCE,
            'handoff/source head')
    require(manifest['sourceBuildHead'] == SOURCE, 'manifest source head')
    require(handoff['manifest']['sha256'] == MANIFEST_SHA and
            handoff['manifest']['path'] == '/workspace/solidity-lean/' + MANIFEST,
            'manifest binding')
    for field in ['gates', 'archives', 'binaries', 'retainedSTOPs']:
        require(handoff[field] == manifest[field], 'metadata disagreement: ' + field)
    require(handoff['runtimeGate'] == manifest['runtimeGate'] == 'pending', 'runtime hold')
    counts = manifest['addressControlsPerBackend']
    require([counts[k] for k in ['fixtureRequests', 'proved', 'refuted', 'unsupported',
                               'additionalPositiveHarnessGuards']] == [16, 10, 2, 4, 2],
            'address denominator')
    gates = handoff['gates']
    require(len(gates) == 24 and len({g['receipt'] for g in gates}) == 24,
            'gate denominator/identity')
    require(sum(g['status'] == 'pass' for g in gates) == 23, 'retained gate failure')
    for gate in gates:
        require((gate['status'] == 'pass' and gate['exitCode'] == 0) or
                (gate['status'] == 'fail' and gate['exitCode'] != 0), 'gate status/exit')
        require(gate['scope'] == {'memoryMaxBytes': 12884901888, 'memorySwapMaxBytes': 0},
                'declared resource scope')
    stops = manifest['retainedSTOPs']
    require(stops['nativeMedianPercent'] == 21.32 and
            stops['browserStartupPercent'] == 32.2 and
            stops['priorNativeBuildIncreasePercent'] == 26.13076760652298,
            'retained performance holds')
    archives = handoff['archives']
    require(len(archives) == 6 and len({a['path'] for a in archives}) == 6,
            'archive denominator/identity')
    relative = []
    for archive in archives:
        prefix = '/workspace/solidity-lean/'
        require(archive['path'].startswith(prefix), 'artifact repository prefix')
        name = archive['path'][len(prefix):]
        path = PurePosixPath(name)
        require(not path.is_absolute() and '..' not in path.parts and str(path) == name,
                'unsafe artifact locator')
        relative.append({**archive, 'repositoryRelative': name})
    return relative


def verify(handoff_path):
    raw = handoff_path.read_bytes()
    require(sha(raw) == HANDOFF_SHA, 'handoff hash')
    manifest_raw = git_bytes(HEAD, MANIFEST)
    require(sha(manifest_raw) == MANIFEST_SHA, 'committed manifest hash')
    handoff, manifest = json.loads(raw), json.loads(manifest_raw)
    archives = check_metadata(handoff, manifest)
    sources = manifest['sourceFiles']
    require(len(sources) == 2 and len({s['path'] for s in sources}) == 2,
            'explicit source pin denominator')
    for source in sources:
        require(sha(git_bytes(SOURCE, source['path'])) == source['sha256'],
                'Git source identity: ' + source['path'])
    return {'guardedRegression': __doc__.splitlines()[0],
            'handoffHead': HEAD, 'sourceBuildHead': SOURCE,
            'handoffSha256': HANDOFF_SHA,
            'manifest': {'gitHead': HEAD, 'repositoryRelative': MANIFEST, 'sha256': MANIFEST_SHA},
            'explicitGitSourcePinsVerified': sources,
            'declaredAddressCounts': manifest['addressControlsPerBackend'],
            'declaredGates': {'total': 24, 'pass': 23, 'fail': 1},
            'retainedSTOPs': manifest['retainedSTOPs'],
            'artifacts': [{**a, 'presentLocally': (ROOT / a['repositoryRelative']).is_file(),
                           'payloadInspected': False} for a in archives],
            'runtimeGate': 'pending', 'execution': False, 'extraction': False,
            'boundary': 'Pinned metadata consistency and two Git source pins only. '
                        'Receipt contents, 343-module runtime source index, selected C objects, '
                        'binaries and request parity remain unverified by this check. '
                        'Local presence never implies payload validation or runtime acceptance.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--handoff', type=Path, default=DEFAULT)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    raw = json.dumps(verify(args.handoff), indent=2) + '\n'
    if args.report:
        args.report.write_text(raw)
    else:
        print(raw, end='')
