#!/usr/bin/env python3
"""Reproduce the frozen pilot; all outputs and temporary trees stay outside Git.

--static reads Git objects and the patch only. A full run creates a NEW worktree,
fetches cache first (unless --cache-ready), builds imports, and measures serial
warm-import elaboration twice per variant. It kernel-checks every old statement
against the emitted theorem and prints every theorem's axiom dependencies.
"""
import argparse, collections, fcntl, hashlib, json, os, pathlib, re, statistics
import subprocess, time
BASE = '772806909ec30c93a85a95c01130a70b6bcc83ca'
ROOT = pathlib.Path(__file__).resolve().parents[4]
HERE = pathlib.Path(__file__).resolve().parent
FILES = ['Solidity/Yul/Checks/Arithmetic/Part00.lean', 'Solidity/Yul/Checks/Bytes.lean']
BINARY = re.compile(r'^theorem (v\d+) : \(Pure.eval \.«([^»]+)» \(fun i => if i.val = 0 then word (\d+) else word (\d+)\)\).val = (\d+) := by decide \+kernel$', re.M)
ROW = re.compile(r'^word_vectors «([^»]+)» (\d+) \[(.*)\]$', re.M)
THEOREM = re.compile(r'^theorem (\w+) : (.+) := by decide \+kernel$', re.M)

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

def patched_sources():
    # Parse this deliberately simple two-file unified diff without mutating a tree.
    old = {p: git('show', BASE + ':' + p) for p in FILES}
    patch = (HERE / 'pilot.patch').read_text()
    assert len(patch.encode()) < 1_000_000
    new = {}
    for section in patch.split('diff --git ')[1:]:
        header, *lines = section.splitlines(keepends=True)
        path = header.split()[1][2:]
        assert path in old
        src = old[path].splitlines(keepends=True); dst = []; pos = 0; in_hunk = False
        for line in lines:
            if line.startswith('@@'):
                start = int(re.match(r'@@ -(\d+)', line)[1]) - 1
                dst.extend(src[pos:start]); pos = start; in_hunk = True
            elif in_hunk:
                if line.startswith(' '):
                    assert src[pos] == line[1:]; dst.append(src[pos]); pos += 1
                elif line.startswith('-'):
                    assert src[pos] == line[1:]; pos += 1
                elif line.startswith('+'): dst.append(line[1:])
                else: raise AssertionError('unexpected patch record: ' + line)
        dst.extend(src[pos:]); new[path] = ''.join(dst)
    assert set(new) == set(old)
    return old, new

def expand(s):
    statements = dict(THEOREM.findall(s))
    for op, a, rows in ROW.findall(s):
        for row in rows.split(', '):
            name, b, result = row.split()
            assert name not in statements
            statements[name] = f'(Pure.eval .«{op}» (fun i => if i.val = 0 then word {a} else word {b})).val = {result}'
    return statements

def inventory():
    # Lexical candidate counts, NOT native declarations or safe deletions.
    areas = collections.defaultdict(lambda: dict(files=0, lines=0, decide_sites=0, theorem_headers=0))
    vectors = {}
    controls = collections.defaultdict(lambda: dict(files=0, lines=0, theorem_headers=0, decide_sites=0))
    corpus = {}
    for p in git('ls-tree', '-r', '--name-only', BASE).splitlines():
        if not p.endswith('.lean'): continue
        s = git('show', BASE + ':' + p)
        n = len(re.findall(r':=\s*by\s+decide(?:\s+\+kernel)?', s))
        if pathlib.Path(p).name.endswith('Controls.lean'):
            a = controls['/'.join(p.split('/')[:2])]; a['files'] += 1; a['lines'] += len(s.splitlines())
            a['theorem_headers'] += len(re.findall(r'^\s*(?:theorem|lemma)\s', s, re.M)); a['decide_sites'] += n
        if p.startswith('Solidity/Corpus/'):
            corpus[p] = dict(lines=len(s.splitlines()), theorem_headers=len(re.findall(r'^\s*theorem\s', s, re.M)), corpus_decide=len(re.findall(r'^\s+corpus_decide\b', s, re.M)))
        if n:
            key = '/'.join(p.split('/')[:2]) if '/' in p else '(roots)'
            a = areas[key]; a['files'] += 1; a['lines'] += len(s.splitlines())
            a['decide_sites'] += n; a['theorem_headers'] += len(re.findall(r'\b(?:theorem|lemma)\s', s))
        if p.startswith('Solidity/Yul/Checks/') and re.search(r'^theorem v\d+', s, re.M):
            binary = len(BINARY.findall(s))
            # Same row grouping and per-file macro overhead as the pilot.
            groups = []
            for _, op, a, b, r in BINARY.findall(s):
                if not groups or groups[-1][:2] != (op, a) or groups[-1][2] == 16:
                    groups.append((op, a, 0))
                x, y, count = groups[-1]; groups[-1] = (x, y, count + 1)
            vectors[p] = dict(vectors=len(re.findall(r'^theorem v\d+', s, re.M)), binary=binary,
                              rows=len(groups), predicted_line_saving=(binary-len(groups)-10 if binary else 0))
    return dict(areas=dict(sorted(areas.items())), vectors=vectors, controls=dict(sorted(controls.items())), corpus=corpus)

def static():
    old, new = patched_sources(); results = {}
    for p in FILES:
        assert expand(old[p]) == expand(new[p]), 'name or literal statement changed'
        for token in ['native_' + 'decide', 'sor' + 'ry', 'axiom ', 'maxHeartbeats']:
            assert token not in new[p]
        results[p] = dict(before_lines=len(old[p].splitlines()), after_lines=len(new[p].splitlines()),
                          before_bytes=len(old[p].encode()), after_bytes=len(new[p].encode()),
                          theorem_constants=len(expand(old[p])), table_vectors=sum(len(r.split(', ')) for _, _, r in ROW.findall(new[p])),
                          rows=len(ROW.findall(new[p])), literal_statements_identical=True,
                          macro_bytes=sum(len(x.encode())+1 for x in new[p].splitlines() if x.startswith(('syntax ', 'macro_rules', '  |', '    ', '      ', '-- Each'))))
    return results

def run(cmd, cwd, log, env):
    with open(log, 'w') as f:
        p = subprocess.run(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
    if p.returncode: raise RuntimeError(f'{cmd} failed ({p.returncode}); see {log}')

def audit_logs(result, out):
    for i, p in enumerate(FILES):
        logs = {}
        for variant in ['before', 'after']:
            log = (out/f'{variant}-{i}-types-axioms.log').read_text()
            lines = [line for line in log.splitlines() if 'depends on axioms:' in line or 'does not depend on any axioms' in line]
            assert len(lines) == result['source'][p]['theorem_constants']
            assert 'sorryAx' not in log
            result['timings'][f'{variant}:{p}']['namespace_native_constants'] = int(re.search(r'namespace_constants: (\d+)', log)[1])
            logs[variant] = lines
        assert logs['before'] == logs['after'], 'axiom dependencies changed'
    result['kernel_audit'] = 'All 1947 old types elaborate against the same named theorems; all axiom lists identical.'
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--static', action='store_true')
    ap.add_argument('--audit-results', type=pathlib.Path, help='validate/enrich existing external measurement logs, without rerunning Lean')
    ap.add_argument('--inventory', action='store_true')
    ap.add_argument('--worktree', type=pathlib.Path)
    ap.add_argument('--out', type=pathlib.Path)
    ap.add_argument('--cache-ready', action='store_true')
    args = ap.parse_args()
    if args.audit_results:
        out = args.audit_results.resolve()
        result = json.loads((out/'measurement.json').read_text())
        assert result['base'] == BASE and result['source'] == static()
        result = audit_logs(result, out)
        (out/'measurement.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result, indent=2)); return
    result = dict(base=BASE, source=static())
    if args.inventory: result['inventory'] = inventory()
    if args.static:
        print(json.dumps(result, indent=2)); return
    if not args.worktree or not args.out: ap.error('full run requires --worktree NEW_PATH --out EXTERNAL_PATH')
    work = args.worktree.resolve(); out = args.out.resolve()
    assert not work.exists(), 'refuse to overwrite a worktree'
    assert not out.is_relative_to(ROOT), 'evidence must stay outside the code tree'
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    lockpath = pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    with lockpath.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not args.cache_ready:
            run(['bash', 'scripts/ci/fetch-lake-cache.sh'], ROOT, out/'cache.log', env)
        run(['git', 'worktree', 'add', '--detach', str(work), BASE], ROOT, out/'worktree.log', env)
        # Imports only: no timing includes a dependency build or artifact-cache hit.
        run(['lake', 'build', 'Solidity.Yul.Words', 'Solidity.KeySort'], work, out/'imports.log', env)
        run(['python3', 'scripts/ci/restore-lake-artifacts.py'], work, out/'restore.log', env)
        result['versions'] = {cmd: subprocess.check_output([cmd, '--version'], env=env, text=True).strip() for cmd in ['lean', 'lake']}
        result['resources'] = dict(lean_threads=1, swap=pathlib.Path('/proc/swaps').read_text(),
                                   check_memory_limit_mib=12288, note='no systemd scope on the cloud VM (H232)')
        result['timings'] = {}
        old, new = patched_sources()
        for variant in ['before', 'after']:
            if variant == 'after':
                run(['git', 'apply', str(HERE/'pilot.patch')], work, out/'apply.log', env)
            for i, p in enumerate(FILES):
                assert (work/p).read_text() == (old if variant == 'before' else new)[p]
                module = p[:-5].replace('/', '.')
                output = work/'.lake/build/lib/lean'/pathlib.Path(p).with_suffix('.olean')
                output.parent.mkdir(parents=True, exist_ok=True)
                cmd = ['lake', 'env', 'lean', '-j1', '-M12288', '--tstack=131072', '-o', str(output), p]
                samples = []
                for rep in range(2):
                    stem = f'{variant}-{i}-{rep}'
                    timer = 'import subprocess,resource,time,sys; t=time.monotonic(); p=subprocess.run(sys.argv[2:]); open(sys.argv[1],"w").write(f"{time.monotonic()-t} {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}\\n"); sys.exit(p.returncode)'
                    timed = ['python3', '-c', timer, str(out/(stem+'.time')), *cmd]
                    run(timed, work, out/(stem+'.log'), env)
                    elapsed, rss = (out/(stem+'.time')).read_text().split()
                    samples.append(dict(seconds=float(elapsed), peak_rss_kib=int(rss)))
                result['timings'][f'{variant}:{p}'] = dict(command=cmd, samples=samples,
                         median_seconds=statistics.median(x['seconds'] for x in samples),
                         max_rss_kib=max(x['peak_rss_kib'] for x in samples), olean_bytes=output.stat().st_size)
                ns = re.search(r'^namespace (.+)$', old[p], re.M)[1]
                checks = ['import Lean', 'import '+module, 'open Solidity.Yul']
                for name, statement in expand(old[p]).items():
                    checks += [f'example : {statement} := @{ns}.{name}', f'#print axioms {ns}.{name}']
                checks += [f'run_cmd do\n  let env ← Lean.getEnv\n  let n := env.constants.fold (fun count name _ => if (`{ns}).isPrefixOf name then count + 1 else count) (0 : Nat)\n  Lean.logInfo m!"namespace_constants: {{n}}"']
                verify = work/f'Verify{i}.lean'; verify.write_text('\n'.join(checks)+'\n')
                run(['lake', 'env', 'lean', '-j1', '-M12288', '--tstack=131072', str(verify)], work, out/f'{variant}-{i}-types-axioms.log', env)
                log = (out/f'{variant}-{i}-types-axioms.log').read_text()
                assert 'sorryAx' not in log and log.count('depends on axioms:') + log.count('does not depend on any axioms') == len(expand(old[p]))
        result = audit_logs(result, out)
        (out/'measurement.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
