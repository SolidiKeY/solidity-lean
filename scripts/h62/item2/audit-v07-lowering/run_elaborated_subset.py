#!/usr/bin/env python3
"""Run under the existing writer-locked resource wrapper; bind sources twice.

Guarded regression: completion markers from a failed or stale inspection are
not successful evidence. Lake checks imported artifacts before running the
exact pinned probe; the caller records its exit/resource receipt.
"""
import argparse
import json
from pathlib import Path
import subprocess
from read_elaborated_subset import check_pins

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--folder', type=Path, required=True)
    args = parser.parse_args()
    repo, folder = args.repo.resolve(), args.folder.resolve()
    _, before = check_pins(repo, folder)
    print('H62_SOURCE_BINDING '+json.dumps(dict(stage='before', **before), sort_keys=True), flush=True)
    subprocess.run(['lake','lean',str(folder/'Probe.lean'),'--',
                    '--root='+str(folder),'--tstack=131072','-j1'],cwd=repo,check=True)
    _, after = check_pins(repo, folder)
    if before != after:
        raise ValueError('inspection inputs changed during execution')
    print('H62_SOURCE_BINDING '+json.dumps(dict(stage='after', **after), sort_keys=True), flush=True)
