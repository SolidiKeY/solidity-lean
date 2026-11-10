#!/usr/bin/env python3
"""Optional H456 comparison recipe; never A04 acceptance by itself.

Guarded regression: path-setup optimization must not omit a public proof input,
accept stale/corrupt objects, skip theorem proofs, or turn a failure into a pass.
Only the delivered failing comparison is supported. Keep VA1's original trust
prelude, immutable overlay generation, serial admission and external resource
wrapper (including its independent 298/300-second deadline) unchanged. This
launcher adds one 300-second TOTAL budget, including its own validation; it
never partitions or retries. Real-corpus validation and adoption belong to VA1.

Optimization: retain `lake env env`, but give the checker LEAN_PATH=overlay and
LEAN_SYSROOT=the same toolchain prefix. Lean4.24 appends its builtin lib/lean;
the reference redundantly supplies it too. The pinned checker scans every path.
No checker source, binary, --fresh behavior, proof domain or exclusion changes.
The original trusted PATH/tool installation is an external precondition, as in
the reference. Supplied sysroot must equal active `lean --print-prefix`; Lake
is the same PATH selector. Their bytes are recorded/checked for stability, not
independently authenticated by new policy. Dirty/untracked Lake context and
unlisted object companions are refused, never silently deleted.

Example (inside the unchanged external VA1 resource guard):
 python3 scripts/trust-replay/recipe.py --packet "$PRIVATE_PACKET" \
   --manifest "$ORIGINAL_OVERLAY/MANIFEST.json" --objects "$ORIGINAL_OVERLAY" \
   --source-root "$VA1_SOURCE_ROOT" --checker "$PINNED_CHECKER" \
   --checker-source "$PINNED_CHECKER_SOURCE" --sysroot "$PINNED_LEAN_PREFIX" \
   --output "$FRESH_PRIVATE_OUTPUT"

Do not reconstruct the original manifest or corpus from packet metadata. There
is no current-head mode: another head needs its own complete freshly generated
manifest and owner review. This optional CLI is not a frozen or mandatory API.
"""
if not __debug__:
    raise SystemExit('optimized Python refused')

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import signal
import shutil
import stat
import subprocess
import time


@dataclass(frozen=True)
class Profile:
    packet_sha256: str
    manifest_sha256: str
    checker_sha256: str
    checker_revision: str
    head: str
    count: int
    total_bytes: int
    root: str = 'Solidity.Theorems'
    seconds: float = 300
    synthetic: bool = False


REFERENCE = Profile(
    '5db9e6d1d55fd6e15813398f86f22b6c373737d01f583e213a0d3b360956fac3',
    'f4783b776e1624a43b50a7d878fb759c9172c490acf32fefff4a5b715be01078',
    '742a92543440bd86238297d7044070e5fa79387ce705f7f268fe4d36b9727461',
    'da26eb05e9959402afcb9bd6dfe5dc4f700f70d6',
    '057db8c12cfda964867a519514e0526c91b00576', 267, 638245176)
TOOLCHAIN = 'leanprover/lean4:v4.24.0'
SCOPE = 'fresh importing setup selects every object including the public root; source type closure is not the proof replay domain'


class InvalidInput(Exception):
    pass


class Deadline(Exception):
    pass


def require(ok, message):
    if not ok:
        raise InvalidInput(message)


def clock():
    return time.clock_gettime(time.CLOCK_BOOTTIME)


def remaining(deadline):
    value = deadline - clock()
    if value <= 0:
        raise Deadline('total comparison deadline exceeded')
    return value


def digest(path, deadline):
    remaining(deadline)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode), 'nonregular input: ' + str(path))
        h = hashlib.sha256()
        while chunk := stream.read(1024 * 1024):
            remaining(deadline)
            h.update(chunk)
        after = os.fstat(stream.fileno())
        require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) ==
                (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns),
                'input changed while hashing: ' + str(path))
    remaining(deadline)
    return h.hexdigest()


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'duplicate JSON key: ' + key)
        out[key] = value
    return out


def load_json(path, expected_hash, deadline):
    require(digest(path, deadline) == expected_hash, 'input SHA256 mismatch: ' + str(path))
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == expected_hash, 'input changed before parse')
    return json.loads(raw, object_pairs_hook=unique_object)


def validate_inputs(profile, packet_path, manifest_path, objects, deadline):
    packet = load_json(packet_path, profile.packet_sha256, deadline)
    require(packet['head'] == profile.head and packet['toolchain'] == TOOLCHAIN and
            packet['checker_revision'] == profile.checker_revision and
            packet['checker_binary_sha256'] == profile.checker_sha256 and
            packet['manifest_sha256'] == profile.manifest_sha256,
            'comparison packet identity mismatch')
    manifest = load_json(manifest_path, profile.manifest_sha256, deadline)
    require(manifest == packet['manifest_content'], 'manifest differs from bound packet')
    require(manifest['schema'] == 1 and type(manifest['schema']) is int and
            manifest['head'] == profile.head and manifest['root'] == profile.root and
            manifest['scope'] == SCOPE, 'manifest schema/head/root/scope mismatch')
    provenance = manifest['provenance']
    require(provenance['setupOrigin'] == 'lake --no-build setup-file (import ' + profile.root + ')' and
            all(re.fullmatch('[0-9a-f]{64}', provenance[k]) for k in ('setupSha256', 'rootSourceSha256')),
            'manifest provenance mismatch')
    files = manifest['files']
    require(isinstance(files, list) and len(files) == profile.count, 'omitted/extra manifest row')
    expected, size = set(), 0
    for row in files:
        remaining(deadline)
        require(set(row) == {'path', 'source', 'sha256', 'bytes'}, 'invalid manifest row fields')
        path = row['path']
        require(isinstance(path, str) and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9/]*\.olean', path), 'unsafe object path')
        require(path not in expected and type(row['bytes']) is int and row['bytes'] >= 0 and
                isinstance(row['source'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']),
                'duplicate or malformed object identity')
        expected.add(path)
        target = objects.joinpath(*PurePosixPath(path).parts)
        for parent in (target, *target.parents):
            if parent == objects:
                break
            require(not parent.is_symlink(), 'object symlink refused: ' + path)
        require(target.is_file() and target.stat().st_size == row['bytes'], 'missing/wrong-size object: ' + path)
        require(digest(target, deadline) == row['sha256'], 'corrupt object: ' + path)
        size += row['bytes']
    require(size == profile.total_bytes, 'object byte total mismatch')
    require(profile.root.replace('.', '/') + '.olean' in expected, 'public root omitted')
    actual = set()
    for path in objects.rglob('*'):
        remaining(deadline)
        require(not path.is_symlink(), 'symlink in immutable object tree')
        require(path.is_dir() or stat.S_ISREG(path.lstat().st_mode),
                'special node in immutable object tree')
        if path.is_file():
            relative = path.relative_to(objects).as_posix()
            require(relative in expected or path == manifest_path,
                    'unlisted input or object companion: ' + relative)
            if path.suffix == '.olean':
                actual.add(relative)
    require(actual == expected, 'unlisted/omitted object in replay tree')
    return manifest


def process(command, cwd, env, deadline, output):
    """Preserve the reference GNU timeout arrangement; do not detach a session.

    The independent external VA1 guard is still required for hard escalation,
    RSS/no-swap enforcement and descendants. GNU timeout carries the remaining
    total budget even if this Python launcher is killed unexpectedly.
    """
    timer = shutil.which('timeout')
    require(timer is not None, 'reference GNU timeout unavailable')
    launcher = [timer, format(remaining(deadline), '.6f'), *command]
    child = None
    interrupted = None
    previous = {}
    def record(signum, frame):
        nonlocal interrupted
        interrupted = signum
    try:
        for sig in (signal.SIGTERM, signal.SIGINT):
            previous[sig] = signal.signal(sig, record)
        child = subprocess.Popen(launcher, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                 stdout=output, stderr=subprocess.STDOUT)
        forwarded = None
        while child.poll() is None:
            if interrupted is not None and interrupted != forwarded:
                try:
                    child.send_signal(interrupted)
                except ProcessLookupError:
                    pass
                forwarded = interrupted
            try:
                child.wait(timeout=.05)
            except subprocess.TimeoutExpired:
                pass
        code = child.returncode
        if interrupted is not None and code == 0:
            code = 128 + interrupted
    finally:
        if child is not None and child.poll() is None:
            # GNU timeout forwards this to the job exactly as in the reference.
            child.terminate()
            child.wait()
        for sig, handler in previous.items():
            signal.signal(sig, handler)
    remaining(deadline)
    return code if code >= 0 else 128 - code


def git_bytes(command, cwd, deadline):
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    result = subprocess.run(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                            capture_output=True, timeout=remaining(deadline))
    require(result.returncode == 0, 'setup command failed: ' + repr(command) + ': ' + result.stderr[-1000:].decode(errors='replace'))
    remaining(deadline)
    return result.stdout


def small(command, cwd, deadline):
    return git_bytes(command, cwd, deadline).decode().strip()


def lake_context(source, head, deadline):
    """Bind the initial context to the selected commit, not just stable bytes."""
    context = {}
    for name in ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json'):
        entry = small(['git', '--no-replace-objects', 'ls-tree', head, '--', name], source, deadline)
        path = source / name
        if not entry:
            require(not path.exists() and not path.is_symlink(), 'untracked Lake context: ' + name)
            continue
        require(entry.startswith(('100644 blob ', '100755 blob ')), 'nonregular committed Lake context')
        expected = hashlib.sha256(git_bytes(['git', '--no-replace-objects', 'show', head + ':' + name], source, deadline)).hexdigest()
        require(digest(path, deadline) == expected, 'dirty Lake context: ' + name)
        context[name] = expected
    return context


def run(profile, config):
    """Synthetic profiles are import-only controls; CLI always uses REFERENCE."""
    start = clock()
    deadline = start + profile.seconds
    paths = {name: Path(value).resolve() for name, value in vars(config).items()}
    output = paths['output']
    protected = [paths[k] for k in ('objects', 'source_root', 'checker_source', 'sysroot')]
    protected += [Path(__file__).resolve().parent]
    for tree in protected:
        require(not output.is_relative_to(tree) and not tree.is_relative_to(output), 'output overlaps protected tree')
    require(not output.exists(), 'fresh private output required')
    output.mkdir(parents=True)
    receipt = {'a04_accepted': False, 'synthetic_control': profile.synthetic,
               'head': profile.head, 'root': profile.root, 'manifest_sha256': profile.manifest_sha256,
               'checker_sha256': profile.checker_sha256, 'checker_revision': profile.checker_revision,
               'object_count': profile.count, 'object_bytes': profile.total_bytes,
               'total_budget_seconds': profile.seconds, 'outer_resource_guard_required': True,
               'validation': 'pending-va1-owner-review-and-real-comparison', 'checker_started': False}
    code = 2
    try:
        manifest = validate_inputs(profile, paths['packet'], paths['manifest'], paths['objects'], deadline)
        require(digest(paths['checker'], deadline) == profile.checker_sha256, 'checker binary mismatch')
        git = ['git', '--no-replace-objects']
        require(small(git + ['rev-parse', 'HEAD'], paths['checker_source'], deadline) == profile.checker_revision,
                'checker source revision mismatch')
        require(not small(git + ['status', '--porcelain'], paths['checker_source'], deadline), 'dirty checker source')
        require(small(git + ['rev-parse', 'HEAD'], paths['source_root'], deadline) == profile.head, 'stale source head')
        for tree in (paths['source_root'], paths['checker_source']):
            require((tree / 'lean-toolchain').read_text().strip() == TOOLCHAIN, 'toolchain file mismatch')
        root_source = paths['source_root'] / (profile.root.replace('.', '/') + '.lean')
        require(digest(root_source, deadline) == manifest['provenance']['rootSourceSha256'], 'stale public root source')
        lean = shutil.which('lean')
        lake = shutil.which('lake')
        require(lean is not None and lake is not None, 'original reference Lean/Lake selectors unavailable')
        active_prefix = Path(small([lean, '--print-prefix'], paths['source_root'], deadline)).resolve()
        require(active_prefix == paths['sysroot'], 'sysroot differs from active reference Lean prefix')
        require(not os.environ.get('LEAN_SYSROOT') or Path(os.environ['LEAN_SYSROOT']).resolve() == active_prefix,
                'ambient LEAN_SYSROOT differs from reference prefix')
        require('version 4.24.0,' in small([lean, '--version'], paths['source_root'], deadline), 'Lean version mismatch')
        require('4.24.0' in small([lake, '--version'], paths['source_root'], deadline), 'Lake version mismatch')
        tools = {str(Path(tool).resolve()): digest(Path(tool).resolve(), deadline) for tool in (lean, lake)}
        context = lake_context(paths['source_root'], profile.head, deadline)
        require(context, 'Lake context unavailable')
        require(all(os.pathsep not in str(paths[k]) for k in ('objects', 'sysroot')), 'search-path separator in directory')
        command = [str(lake), 'env', 'env', 'LEAN_NUM_THREADS=1',
                   'LEAN_SYSROOT=' + str(paths['sysroot']), 'LEAN_PATH=' + str(paths['objects']),
                   str(paths['checker']), '--fresh', profile.root]
        receipt['command'] = command
        receipt['lake_context_sha256'] = context
        receipt['reference_tools_sha256'] = tools
        receipt['sysroot_authentication'] = 'unchanged external VA1 pinned installation/guard required; not independently attested by this recipe'
        env = dict(os.environ, LEAN_NUM_THREADS='1')
        with (output / 'checker.log').open('wb') as log:
            receipt['checker_started'] = True
            code = process(command, paths['source_root'], env, deadline, log)
        receipt['checker_exit_code'] = code
        # Failure and timeout never acquire success credit through post-validation.
        if code == 0:
            validate_inputs(profile, paths['packet'], paths['manifest'], paths['objects'], deadline)
            require(digest(paths['checker'], deadline) == profile.checker_sha256, 'checker changed during replay')
            require(digest(root_source, deadline) == manifest['provenance']['rootSourceSha256'], 'public root changed')
            require(small(git + ['rev-parse', 'HEAD'], paths['source_root'], deadline) == profile.head, 'source head changed')
            require(small(git + ['rev-parse', 'HEAD'], paths['checker_source'], deadline) == profile.checker_revision and
                    not small(git + ['status', '--porcelain'], paths['checker_source'], deadline), 'checker source changed')
            require(context == lake_context(paths['source_root'], profile.head, deadline), 'Lake context changed')
            require(tools == {path: digest(Path(path), deadline) for path in tools}, 'reference tool changed')
            require(Path(small([lean, '--print-prefix'], paths['source_root'], deadline)).resolve() == paths['sysroot'],
                    'active reference prefix changed')
            require(all((tree / 'lean-toolchain').read_text().strip() == TOOLCHAIN for tree in
                        (paths['source_root'], paths['checker_source'])), 'toolchain file changed')
        receipt['candidate_exit_code'] = code
    except (Deadline, subprocess.TimeoutExpired) as error:
        code = 124
        receipt.update(candidate_exit_code=code, error=str(error))
    except (InvalidInput, OSError, ValueError, KeyError, TypeError) as error:
        code = 2
        receipt.update(candidate_exit_code=code, error=str(error))
    receipt['elapsed_seconds'] = clock() - start
    (output / 'candidate-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for option in ('packet', 'manifest', 'objects', 'source-root', 'checker', 'checker-source', 'sysroot', 'output'):
        parser.add_argument('--' + option, required=True, type=Path)
    config = parser.parse_args()
    return run(REFERENCE, config)


if __name__ == '__main__':
    raise SystemExit(main())
