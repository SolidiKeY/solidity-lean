#!/usr/bin/env python3
"""Read-only production-input census and lease guard; JSON goes to stdout."""
import hashlib, json, pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
INPUTS = [
    'Solidity/Lowering/V08/ConstructorScalarTransport.lean',
    'Solidity/Lowering/V08/CreationPremises.lean',
    'Solidity/Lowering/V08/LibraryFrameTransport.lean',
    'Solidity/Lowering/V08/LibraryPremises.lean',
    'Solidity/Lowering/V07/P8Bindings.lean',
    'Solidity/Lowering/P8/FrozenInterface.lean',
]

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def main():
    git('merge-base', '--is-ancestor', BASE, 'HEAD')
    files = []
    for name in INPUTS:
        current = (ROOT/name).read_bytes()
        original = git('show', BASE+':'+name)
        files.append(dict(path=name, sha256=hashlib.sha256(current).hexdigest(),
                          base_sha256=hashlib.sha256(original).hexdigest(), unchanged=current==original))
    changed = set(git('diff', '--name-only', '-z', BASE).decode().split('\0'))
    changed.update(git('ls-files', '--others', '--exclude-standard', '-z').decode().split('\0'))
    changed.discard('')
    allowed = lambda name: (name.startswith('tests/h55/v08-agreements/') or
                            name.startswith('scripts/h55/v08-agreements/') or
                            name == 'docs/feature-work/h55-v08-agreements.md')
    forbidden = sorted(name for name in changed if not allowed(name))
    source = ROOT/'tests/h55/v08-agreements/Agreements.lean'
    result = dict(base=BASE, head=git('rev-parse','HEAD').decode().strip(), repository=str(ROOT),
                  branch=git('branch','--show-current').decode().strip(), inputs=files,
                  changed=sorted(changed), forbidden=forbidden,
                  candidate_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  source_preserved=all(item['unchanged'] for item in files),
                  lease_pass=not forbidden)
    print(json.dumps(result, indent=2))
    return 0 if result['source_preserved'] and result['lease_pass'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
