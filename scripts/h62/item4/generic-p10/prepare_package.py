#!/usr/bin/env python3
"""Pin the standalone test package to the frozen Bridge dependency manifest.

Shares only ignored dependency/build storage on this VM. Never runs `lake
update`, edits the owner manifest, or changes revisions.
"""
import argparse
import json
from pathlib import Path
import subprocess
import census


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    repo = args.repo.resolve()
    package = repo/'tests/h62/item4/generic-p10'
    source = repo/'Bridge/lake-manifest.json'
    frozen = subprocess.check_output(['git', '-C', str(repo), 'show', f'{census.BASE}:Bridge/lake-manifest.json'])
    if source.read_bytes() != frozen: raise SystemExit('owner manifest changed; request a relay')
    data = json.loads(frozen)
    data['name'] = '«generic-p10»'
    for entry in data['packages']:
        entry['inherited'] = True
        if entry['type'] == 'path':
            if entry['name'] != '«solidity-lean»': raise ValueError('unexpected path dependency')
            entry['dir'] = '../../../..'
    data['packages'].append(dict(type='path', scope='', name='«solidity-bridge»',
        manifestFile='lake-manifest.json', inherited=False, dir='../../../../Bridge', configFile='lakefile.toml'))
    data['packagesDir'] = '.lake/packages'
    expected = json.dumps(data, indent=2, sort_keys=True)+'\n'
    manifest = package/'lake-manifest.json'
    lake = package/'.lake'
    target = repo/'Bridge/.lake/packages'
    if lake.is_symlink() or (lake.exists() and not lake.is_dir()): raise ValueError('preserve unexpected .lake')
    link = lake/'packages'
    if args.check:
        if manifest.read_text() != expected or not link.is_symlink() or link.resolve() != target.resolve():
            raise SystemExit('standalone package is not reproducible')
    else:
        if manifest.is_symlink() or (manifest.exists() and manifest.read_text() != expected):
            raise ValueError('preserve unexpected test manifest')
        if not manifest.exists():
            with manifest.open('x') as stream: stream.write(expected)
        lake.mkdir(exist_ok=True)
        if link.is_symlink():
            if link.resolve() != target.resolve(): raise ValueError('preserve unexpected packages link')
        elif link.exists(): raise ValueError('preserve unexpected packages directory')
        else: link.symlink_to(target, target_is_directory=True)
    print('TEST_PACKAGE_SOURCE_PASS: same pinned dependency revisions; owner manifest untouched')


if __name__ == '__main__': main()
