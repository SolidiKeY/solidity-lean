#!/usr/bin/env python3
"""H534 metadata-only candidate inspection; never a replay or CI entry point.

Guards against substituting checker sources, treating empty opaque fallbacks as
native correspondence, or mistaking synthetic controls for public validation.
Use git apply --unidiff-zero for the adjacent self-contained patch to a local checkout of BASE, commit its
four files, then supply that isolated checkout. Frozen v1/v2 remain untouched.
Requires the external serial/no-swap/memory/300-second guard and explicit cloud
opt-in. Builds only the candidate and metadata controls; no checker executable
is run. Public imports, real-domain checks and ANY kernel replay are refused by
this interface. A later comparison requires separate approval and a new runner.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

BASE = 'da26eb05e9959402afcb9bd6dfe5dc4f700f70d6'
PATCH_SHA = 'c5a848c591d1758a6bd86d9297fc20aa8356e7f87333d06f5affc31903f05fd8'
SOURCES = {'Main.lean': 'd73db540ff418bba732561502bda86b1ea3f853cef39ede62ed5b386d81007bd', 'Lean4Checker/Replay.lean': '0d38687c503453626609481084300b25f3bfa86fae5d1ee991ee4bb3115b77f3', 'Lean4Checker/FusedDepsV3.lean': 'e5204f71b564aa66d032145c74496c7737fea2befb2fdf719daae7725a43e7b1', 'Lean4Checker/FusedDepsV3Controls.lean': '68c6376704a7815d7a8626aa4790e4cb0f6cc128117c8657ec537b7d867491c8'}
TOOLS = {
    'lean': '8fadc3ed92cc9decb94c96ee9c0876e91e03a3a5e69138f32114f02789e2766c',
    'lake': '5f3828d1d1977654cf5602c40ac4ee52b64f7dcf34d64c5877d7b7d2d3616344',
}


class Refused(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Refused(message)


def remaining(deadline):
    seconds = deadline - time.clock_gettime(time.CLOCK_BOOTTIME)
    require(seconds > 0, 'total metadata-control deadline exhausted')
    return seconds


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def call(command, root, deadline, env=None):
    result = subprocess.run(command, cwd=root, env=env, capture_output=True,
                            text=True, timeout=remaining(deadline), check=True)
    remaining(deadline)
    return result.stdout


def inspect_candidate(root, deadline):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'isolated candidate directory required')
    git = ['git', '--no-replace-objects', '-c', 'core.quotePath=false']
    require(not call(git + ['status', '--porcelain', '--untracked-files=all'], root, deadline).strip(),
            'candidate source checkout is dirty')
    revision = call(git + ['rev-parse', 'HEAD'], root, deadline).strip()
    require(revision != BASE, 'v3 needs a distinct derived source identity')
    call(git + ['merge-base', '--is-ancestor', BASE, revision], root, deadline)
    changed = call(git + ['diff', '--name-only', BASE, revision], root, deadline)
    require(set(changed.splitlines()) == set(SOURCES), 'unexpected checker source set')
    for name, expected in SOURCES.items():
        path = root / name
        require(not any(p.is_symlink() for p in (path, *path.parents)), 'source symlink refused')
        require(digest(path) == expected, 'unreviewed checker source: ' + name)
        remaining(deadline)
    patch = Path(__file__).with_name('trust-checker-v3.patch')
    require(digest(patch) == PATCH_SHA, 'candidate patch changed')
    return revision


def check_guards():
    require(os.environ.get('TRUST_CLOUD_NO_SYSTEMD') == '1', 'explicit H232 cloud opt-in required')
    require(os.environ.get('TRUST_V3_METADATA_ONLY') == '1', 'metadata-only opt-in required')
    require(os.environ.get('LEAN_NUM_THREADS') == '1', 'one Lean thread required')
    require(len(Path('/proc/swaps').read_text().splitlines()) == 1, 'swap must be disabled')
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    require(0 < soft <= 15 * 1024**3 and 0 < hard <= 15 * 1024**3,
            'external bounded-memory guard required')
    require(os.environ.get('TRUST_BUDGET_RECORD'), 'external total-deadline guard required')


def run_metadata(root, sysroot, deadline):
    check_guards()
    revision = inspect_candidate(root, deadline)
    sysroot = Path(sysroot).resolve()
    for tool, expected in TOOLS.items():
        require(digest(sysroot / 'bin' / tool) == expected, 'pinned tool binary mismatch: ' + tool)
        remaining(deadline)
    lake = str(sysroot / 'bin/lake')
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_SYSROOT=str(sysroot))
    # Prevent ambient search paths from replacing the isolated compiled helper.
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    version = call([str(sysroot / 'bin/lean'), '--version'], root, deadline, env)
    require('version 4.24.0,' in version, 'Lean 4.24 required')
    build = call([lake, 'build', 'Lean4Checker.FusedDepsV3Controls', 'lean4checker'], root, deadline, env)
    print(build, end='')
    binary = Path(root) / '.lake/build/bin/lean4checker'
    binary_sha = digest(binary)
    control_artifacts = {str(p.relative_to(root)): digest(p) for p in
                         sorted((Path(root) / '.lake/build/lib/lean/Lean4Checker').glob('FusedDepsV3*.olean'))}
    require(len(control_artifacts) == 2, 'missing metadata helper/control objects')
    # --run executes only the metadata fixture main; it imports no Replay/Main,
    # public module or external proof objects and never invokes the checker.
    output = call([lake, 'env', 'lean', '-j1', '--run', 'Lean4Checker/FusedDepsV3Controls.lean'],
                  root, deadline, env)
    require(output.strip() == 'V3_METADATA_CONTROLS_PASS 29 cases; negative oracle rejected; no replay',
            'metadata controls did not complete')
    print(output, end='')
    require(inspect_candidate(root, deadline) == revision, 'candidate changed during controls')
    require(digest(binary) == binary_sha, 'candidate binary changed during controls')
    for name, expected in control_artifacts.items():
        require(digest(Path(root) / name) == expected, 'metadata object changed during controls')
        remaining(deadline)
    print(json.dumps({'candidate_revision': revision, 'checker_sha256': binary_sha,
                      'metadata_objects': control_artifacts, 'metadata_controls_pass': True,
                      'a04_accepted': False, 'public_imports': False, 'replay_performed': False}, sort_keys=True))
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata-only', required=True, action='store_true')
    parser.add_argument('--checker-source', required=True, type=Path)
    parser.add_argument('--sysroot', required=True, type=Path)
    args = parser.parse_args(argv)
    deadline = time.clock_gettime(time.CLOCK_BOOTTIME) + 300
    try:
        return run_metadata(args.checker_source, args.sysroot, deadline)
    except (Refused, OSError, subprocess.SubprocessError) as error:
        print('v3 metadata-only refused: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
