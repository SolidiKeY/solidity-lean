#!/usr/bin/env python3
"""Reproduce a cache-free, serial migration census and bounded directory build.

All outputs and private Lake configuration live outside the source checkout.
No source file, proof budget, toolchain selector or registration is rewritten.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import time

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
AREA = Path('Solidity/SolcValidation')
TARGET = 'Solidity.SolcValidation.DataResolution'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def census(root):
    subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, 'HEAD'], cwd=root, check=True)
    modules = {}
    for path in sorted((root / AREA).glob('*.lean')):
        frozen = subprocess.check_output(['git', 'show', f'{BASE}:{path.relative_to(root)}'], cwd=root)
        if frozen != path.read_bytes():
            raise RuntimeError(f'frozen source differs: {path}')
        text = path.read_text()
        declarations = []
        starts = list(re.finditer(r'(?m)^(private )?(abbrev|inductive|structure|def|theorem) ([^\s:{(]+)', text))
        for i, match in enumerate(starts):
            block = text[match.start():starts[i+1].start() if i+1 < len(starts) else len(text)]
            declarations.append({'name': match[3], 'kind': match[2], 'private': bool(match[1]),
                                 'line': text[:match.start()].count('\n') + 1,
                                 'block_sha256': sha(block.encode())})
        modules[str(path.relative_to(root))] = {
            'source_sha256': sha(path.read_bytes()),
            'imports': re.findall(r'(?m)^import (\S+)', text),
            'declarations': declarations,
            'constructors': re.findall(r'(?m)^  \| ([^\n]+)', text) if 'inductive ' in text else [],
            'proof_budget_options': re.findall(r'(?m)^.*set_option.*$', text),
            'forbidden_tokens': re.findall(r'\b(?:sorry|axiom|native_decide)\b', text)}
    edges = [(p, m) for p, row in modules.items() for m in row['imports']]
    inbound = []
    # Pin reverse importers to the original tree, not newly staged overlay tests.
    matches = subprocess.run(['git', 'grep', '-l', '-e',
                              r'^import Solidity\.SolcValidation\.', BASE,
                              '--', '*.lean'], cwd=root, text=True, capture_output=True)
    if matches.returncode not in (0, 1):
        raise RuntimeError(matches.stderr)
    for entry in matches.stdout.splitlines():
        relative = entry.split(':', 1)[1]
        if AREA in Path(relative).parents:
            continue
        frozen_text = subprocess.check_output(['git', 'show', f'{BASE}:{relative}'],
                                               cwd=root, text=True)
        for imp in re.findall(r'(?m)^import (\S+)', frozen_text):
            if imp.startswith('Solidity.SolcValidation.'):
                inbound.append([relative, imp])
    return {'base': BASE, 'modules': modules, 'edges': edges, 'external_dependency':
            'Solidity.Yul.Builtins', 'inbound': inbound,
            'boundary': 'Syntax and checked local label resolution only; no compiler authentication, execution, layout provenance or gas adequacy.'}


def prepare(root, dest):
    dest.mkdir(parents=True, exist_ok=False)
    # Exact source closure, including the prerequisite KeySort and sort checker.
    todo = [TARGET, 'SolkeyCheck']
    seen = set()
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = Path(mod.replace('.', '/') + '.lean')
        source = root / path
        if not source.exists():
            raise RuntimeError(f'missing local dependency {mod}')
        target = dest / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        for imp in re.findall(r'(?m)^import (\S+)', source.read_text()):
            if imp.startswith('Solidity.'):
                todo.append(imp)
    (dest / 'lakefile.toml').write_text('''name = "solcvalidation-migration"
version = "0.1.0"
enableArtifactCache = false
[[lean_lib]]
name = "Solidity"
weakLeanArgs = ["--tstack=131072", "-j1"]
[[lean_exe]]
name = "solkeycheck"
root = "SolkeyCheck"
weakLeanArgs = ["--tstack=131072", "-j1"]
''')
    (dest / 'source-manifest.json').write_text(json.dumps({
        mod: sha((dest / (mod.replace('.', '/') + '.lean')).read_bytes()) for mod in sorted(seen)
    }, indent=2) + '\n')
    return sorted(seen)



def prepare_full(root, dest, toolchain):
    """Fresh pinned-base repository export; only private test config differs."""
    if toolchain is None:
        raise RuntimeError('prepare-full requires --toolchain')
    lean_version = subprocess.check_output([str(toolchain / 'bin/lean'), '--version'], text=True).strip()
    match = re.search(r'version (4\.(?:24|35)\.0)', lean_version)
    if match is None:
        raise RuntimeError(f'unexpected migration toolchain: {lean_version}')
    dest.mkdir(parents=True, exist_ok=False)
    archive = subprocess.Popen(['git', 'archive', BASE], cwd=root, stdout=subprocess.PIPE)
    try:
        subprocess.run(['tar', '-x', '-C', str(dest)], stdin=archive.stdout, check=True)
    finally:
        archive.stdout.close()
    if archive.wait() != 0:
        raise RuntimeError('pinned-base archive failed')
    subprocess.run(['git', 'init', '-q', str(dest)], check=True)
    original = (dest / 'lakefile.toml').read_text()
    config = original.replace('enableArtifactCache = true', 'enableArtifactCache = false')
    # Every library and executable, including LeanTeX, gets explicit -j1.
    parts = re.split(r'(\[\[lean_(?:lib|exe)\]\])', config)
    for index in range(1, len(parts), 2):
        body = parts[index + 1]
        if 'weakLeanArgs =' in body:
            body = body.replace('weakLeanArgs = ["--tstack=131072"]',
                                'weakLeanArgs = ["--tstack=131072", "-j1"]')
        else:
            body = '\nweakLeanArgs = ["--tstack=131072", "-j1"]' + body
        parts[index + 1] = body
    config = ''.join(parts)
    (dest / 'lakefile.toml').write_text(config)
    (dest / 'lean-toolchain').write_text('leanprover/lean4:v' + match[1] + '\n')
    sources = {str(path.relative_to(dest)): sha(path.read_bytes())
               for path in sorted(dest.rglob('*.lean'))}
    metadata = {'base': BASE, 'lean_version': lean_version,
                'lake_version': subprocess.check_output([str(toolchain / 'bin/lake'), '--version'], text=True).strip(),
                'original_lakefile_sha256': sha(original.encode()),
                'private_lakefile_sha256': sha(config.encode()), 'lean_sources': sources,
                'clean_build_dir_absent': not (dest / '.lake').exists()}
    dest.with_name(dest.name + '-sources.json').write_text(json.dumps(metadata, indent=2) + '\n')
    return metadata['private_lakefile_sha256']


def bounded(command, cwd, toolchain, evidence):
    evidence.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(PATH=str(toolchain / 'bin') + ':' + env.get('PATH', ''),
               LEAN_NUM_THREADS='1', XDG_CACHE_HOME=str(cwd / '.private-cache'))
    cap = 12 * 1024**3
    reserve = 4 * 1024**3
    def headroom():
        mem = dict((k, int(v.split()[0]) * 1024) for k, v in
                   (line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines()))
        cgroup = Path('/sys/fs/cgroup')
        stats = dict(line.split() for line in (cgroup / 'memory.stat').read_text().splitlines())
        # Inactive file cache is reclaimable; reserve available memory, not
        # virtual address space or unreclaimed cache pages. The hard VM cap stays.
        available = (int((cgroup / 'memory.max').read_text()) -
                     int((cgroup / 'memory.current').read_text()) +
                     int(stats.get('inactive_file', 0)))
        return min(mem['MemAvailable'], available)
    if headroom() < reserve:
        raise RuntimeError('4 GiB headroom prerequisite failed')
    if int(Path('/sys/fs/cgroup/memory.swap.current').read_text()) != 0:
        raise RuntimeError('swap is in use')
    def limits():
        os.setsid()
    start = time.monotonic()
    peak = 0
    stopped = None
    with evidence.with_suffix('.log').open('w') as log:
        proc = subprocess.Popen(command, cwd=cwd, env=env,
                                stdout=log, stderr=subprocess.STDOUT, preexec_fn=limits)
        while proc.poll() is None:
            rss = 0
            for stat in Path('/proc').glob('[0-9]*/stat'):
                try:
                    fields = stat.read_text().rsplit(')', 1)[1].split()
                    if int(fields[2]) == proc.pid:
                        rss += int(fields[21]) * os.sysconf('SC_PAGE_SIZE')
                except (OSError, ValueError, IndexError):
                    pass
            peak = max(peak, rss)
            if rss > cap or headroom() < reserve:
                stopped = 'RESOURCE_STOP'
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                break
            time.sleep(0.05)
        code = proc.wait()
        if stopped:
            code = 125
    result = {'command': command, 'cwd': str(cwd), 'toolchain': str(toolchain),
              'exit': code, 'wall_seconds': time.monotonic()-start,
              'kernel_children_maxrss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
              'aggregate_sampled_peak_rss_bytes': peak, 'resource_stop': stopped,
              'limits': {'virtual_address_limit_bytes': None,
                         'rss_watchdog_cap_bytes': cap,
                         'vm_hard_memory_cap_bytes': int(Path('/sys/fs/cgroup/memory.max').read_text()),
                         'reserve_bytes': reserve,
                         'threads': 1, 'swap_current_bytes': 0},
              'log': str(evidence.with_suffix('.log'))}
    evidence.with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)
    return code


def main():
    p = argparse.ArgumentParser()
    p.add_argument('action', choices=['census', 'audit', 'prepare', 'prepare-full', 'run'])
    p.add_argument('--root', type=Path, default=Path.cwd())
    p.add_argument('--dest', type=Path, required=True)
    p.add_argument('--toolchain', type=Path)
    argv = sys.argv[1:]
    separator = argv.index('--') if '--' in argv else len(argv)
    a = p.parse_args(argv[:separator])
    a.command = argv[separator+1:]
    if a.action == 'census':
        a.dest.write_text(json.dumps(census(a.root), indent=2) + '\n')
    elif a.action == 'audit':
        rows = census(a.root)
        lines = ['import Solidity.SolcValidation.DataResolution',
                 'set_option pp.universes true', 'set_option pp.fullNames true']
        for row in rows['modules'].values():
            for declaration in row['declarations']:
                if declaration['private']:
                    continue
                name = 'Solidity.SolcValidation.' + declaration['name']
                lines.append('#check ' + name)
                if declaration['kind'] == 'theorem':
                    lines.append('#print axioms ' + name)
        a.dest.write_text('\n'.join(lines) + '\n')
    elif a.action == 'prepare-full':
        print(prepare_full(a.root, a.dest, a.toolchain))
    elif a.action == 'prepare':
        print(json.dumps(prepare(a.root, a.dest)))
    else:
        command = a.command[1:] if a.command[:1] == ['--'] else a.command
        if not command or not a.toolchain:
            p.error('run needs --toolchain and -- COMMAND')
        raise SystemExit(bounded(command, a.root, a.toolchain, a.dest))

if __name__ == '__main__':
    main()
