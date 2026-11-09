#!/usr/bin/env python3
"""Reproduce the pinned declaration-macro pilot in a fresh owned worktree.

Source counts: --out DIR. Kernel checks/timing: add --lean [--repeats N].
Fetch the published cache first (unless --skip-cache, for an already fetched cache).
All outputs, including generated type/axiom checks, stay outside the code branch.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import time

BASE = '772806909ec30c93a85a95c01130a70b6bcc83ca'
HERE = Path(__file__).resolve().parent
ROOT = Path(subprocess.check_output(['git', '-C', str(HERE), 'rev-parse', '--show-toplevel'], text=True).strip())
INDICES = (1, 2, 3, 4, 5, 6, 7, 9, 10)
FILES = [f'Solidity/TestSuite/Derived{i}.lean' for i in INDICES]
SUPPORT = 'Solidity/TestSuite/ScopedProblems.lean'
CHECKER = 'scripts/check-automatic.mjs'
PAT = re.compile(r'theorem (Solkey\.TestSuite\.\w+)\.proved : ⊢ \1\.problem := by\n  sol_prove')
DECL = re.compile(r'^\s*(?:theorem|lemma|def|abbrev|macro)\b', re.M)


def run(args, cwd=ROOT, **kw):
    return subprocess.run(args, cwd=cwd, check=True, text=True, **kw)


def source(rev, path):
    return subprocess.check_output(['git', 'show', f'{rev}:{path}'], cwd=ROOT, text=True)


def stats(texts):
    texts = list(texts)
    return dict(physical_lines=sum(len(t.splitlines()) for t in texts),
                bytes=sum(len(t.encode()) for t in texts),
                lexical_declarations=sum(len(DECL.findall(t)) for t in texts))


def summarize(data):
    rows=data['runs']
    return {v: dict(seconds_by_repeat=[sum(r['seconds'] for r in rows if r['variant']==v and r['repeat']==i) for i in sorted({r['repeat'] for r in rows})],
                    median_seconds=statistics.median(sum(r['seconds'] for r in rows if r['variant']==v and r['repeat']==i) for i in sorted({r['repeat'] for r in rows})),
                    peak_kib=max(r['peak_kib'] for r in rows if r['variant']==v),
                    kernel_constants=sum(r['constants'] for r in data['kernel_declarations'][v]),
                    kernel_theorems=sum(r['theorems'] for r in data['kernel_declarations'][v])) for v in ('before','after')}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path)
    ap.add_argument('--summarize', type=Path, help='summarize an existing successful measurement without Lean')
    ap.add_argument('--lean', action='store_true')
    ap.add_argument('--consumer', action='store_true', help='include the source-scanner adapter and check record parity')
    ap.add_argument('--inventory', action='store_true', help='regenerate and filter the frozen reachability clusters')
    ap.add_argument('--skip-cache', action='store_true')
    ap.add_argument('--repeats', type=int, default=3)
    a = ap.parse_args()
    if a.summarize:
        data=json.loads(a.summarize.read_text())
        assert data['base']==BASE and data['patch_sha256']==hashlib.sha256((HERE/'pilot.patch').read_bytes()).hexdigest()
        print(json.dumps(summarize(data), indent=2))
        return
    if a.out is None:
        ap.error('--out is required unless --summarize is used')
    if a.lean and any(shutil.which(x) is None for x in ('lean','lake')):
        ap.error('put the pinned lean and lake on PATH')
    if a.lean and not hasattr(os, 'wait4'):
        ap.error('Linux wait4 is required for per-command peak RSS')
    if a.repeats < 1:
        ap.error('--repeats must be positive')
    out = a.out.resolve()
    if out == ROOT or ROOT in out.parents:
        ap.error('outputs must be outside the lane checkout')
    out.mkdir(parents=True, exist_ok=True)
    lockpath = Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    with lockpath.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        tree = out / 'tree'
        if tree.exists():
            ap.error('use a fresh output directory; existing worktrees are never reset')
        run(['git', 'worktree', 'add', '--detach', str(tree), BASE], stdout=subprocess.DEVNULL)
        before = {p: source(BASE, p) for p in [SUPPORT] + FILES + ([CHECKER] if a.consumer else [])}
        names = {p: PAT.findall(before[p]) for p in FILES}
        assert all(len(names[p]) == len(re.findall(r'^theorem ', before[p], re.M)) for p in FILES)
        run(['git', 'apply', '--unidiff-zero', str(HERE / 'pilot.patch')], cwd=tree)
        if a.consumer:
            lean_snapshot={p: (tree/p).read_bytes() for p in [SUPPORT]+FILES}
            run(['git', 'apply', '--unidiff-zero', str(HERE/'consumer.patch')], cwd=tree)
            assert all((tree/p).read_bytes()==t for p,t in lean_snapshot.items()), 'consumer adapter changed Lean inputs'
        changed = subprocess.check_output(['git', 'diff', '--name-only'], cwd=tree, text=True).splitlines()
        assert set(changed) == set(before), changed
        after = {p: (tree / p).read_text() for p in before}
        assert all(not re.search(r'\b(?:sorry|axiom|native_decide|maxHeartbeats)\b',
                                 l[1:]) for l in (HERE / 'pilot.patch').read_text().splitlines()
                   if l.startswith('+') and not l.startswith('+++'))
        for p in FILES:
            assert re.findall(r'^  (Solkey\.TestSuite\.\w+)$', after[p], re.M) == names[p]
            assert 'solkey_prove_batch\n' in after[p]
        full = [source(BASE, f'Solidity/TestSuite/Derived{i}.lean') for i in range(1, 13)]
        rollout = sum(len(PAT.findall(t)) for t in full)
        result = dict(base=BASE, patch_sha256=hashlib.sha256((HERE/'pilot.patch').read_bytes()).hexdigest(),
                      cluster_files=len(FILES), names=sum(map(len, names.values())),
                      before=stats(before.values()), after=stats(after.values()),
                      derived_before=stats(before[p] for p in FILES),
                      derived_after=stats(after[p] for p in FILES),
                      projected_derived_files=12, projected_derived_matching_theorems=rollout,
                      projected_derived_lines=sum(len(t.splitlines()) for t in full),
                      rollout_line_saving=2*rollout-2*12-11,
                      limits='serial -j1 / LEAN_NUM_THREADS=1; no systemd scope on the cloud VM (H232)')
        if a.consumer:
            original=tree/'scripts/duplicates-original-automatic.mjs'
            original.write_text(before[CHECKER])
            fixture=out/'consumer-before.json'
            fixture.write_text(json.dumps({p: before[p] for p in FILES}))
            js = '''import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {proofs as old} from './scripts/duplicates-original-automatic.mjs';
import {proofs as next} from './scripts/check-automatic.mjs';
const before=JSON.parse(readFileSync(process.argv[1], 'utf8'));
let names=0, unadapted=0;
for (const [path, text] of Object.entries(before)) {
  const after=readFileSync(path, 'utf8');
  assert.deepEqual(next(after), old(text));
  names+=old(text).length;
  unadapted+=old(after).length;
}
assert.equal(names, 358);
assert.equal(unadapted, 0);
assert.throws(() => next('solkey_prove_batch\\n  exact foo'));
assert.throws(() => next('solkey_prove_batch'));
assert.ok(next('set_option maxRecDepth 8192 in\\nsolkey_prove_batch\\n  Solkey.TestSuite.foo')[0].opts);
console.log(`PASS source scanner: ${names} original records preserved; empty/manual rows rejected; option classification retained`);
'''
            with (out/'consumer.log').open('w') as log:
                run(['node', '--input-type=module', '-e', js, str(fixture)], cwd=tree, stdout=log, stderr=subprocess.STDOUT)
            delta=len(after[CHECKER].splitlines())-len(before[CHECKER].splitlines())
            result['consumer_adapter_lines']=delta
            result['consumer_adapter_bytes']=len(after[CHECKER].encode())-len(before[CHECKER].encode())
            result['consumer_patch_sha256']=hashlib.sha256((HERE/'consumer.patch').read_bytes()).hexdigest()
            result['rollout_line_saving']-=delta
            result['consumer']='358 original scanner records identical; malformed/manual rows rejected; options retained'
            result['lean_after_sha256']={p: hashlib.sha256(after[p].encode()).hexdigest() for p in [SUPPORT]+FILES}
        if a.inventory:
            path=ROOT/'docs/audits/direction-tools/reachability/reach.py'
            spec=importlib.util.spec_from_file_location('duplicates_inventory', path)
            inventory=importlib.util.module_from_spec(spec)
            spec.loader.exec_module(inventory)
            _, _, nodes, modules, texts, generators, _ = inventory.build()
            totals, clusters = inventory.duplicates(nodes, modules, texts, generators)
            eligible=[c for c in clusters if not any(m.startswith(('Solidity.Backend.', 'Solidity.Lowering.', 'Solidity.Yul.Views.')) for m in c['modules'])]
            near=[c for c in eligible if c['kind']=='near_file']
            result['inventory']=dict(base=inventory.BASE, totals=totals,
                eligible_statement_clusters=len(eligible)-len(near),
                eligible_near_clusters=len(near), eligible_near_lines=sum(c['lines'] for c in near),
                top_three=eligible[:3])
            (out/'clusters.json').write_text(json.dumps(eligible, indent=2)+'\n')
        if a.lean:
            env = dict(os.environ, LEAN_NUM_THREADS='1')
            env.setdefault('LAKE_CACHE_DIR', str(Path(shutil.which('lean')).resolve().parent.parent/'lake/cache'))
            result['cache_dir'] = env['LAKE_CACHE_DIR']
            result['measurement_method'] = 'perf_counter wall seconds; Linux wait4 ru_maxrss KiB, maximum-process RSS, not aggregate RSS'
            result['versions'] = {x: subprocess.check_output([x, '--version'], env=env, text=True).strip() for x in ('lean', 'lake')}
            if not a.skip_cache:
                with (out/'cache.log').open('w') as log:
                    run(['bash', 'scripts/ci/fetch-lake-cache.sh'], cwd=tree, env=env, stdout=log, stderr=subprocess.STDOUT)
            # Build imports outside timing, at the exact base. Both variants share these artifacts.
            run(['git', 'apply', '-R', '--unidiff-zero', str(HERE/'pilot.patch')], cwd=tree)
            with (out/'imports.log').open('w') as log:
                run(['lake', 'build', 'Solidity.TestSuite.ScopedProblems'], cwd=tree, env=env, stdout=log, stderr=subprocess.STDOUT)
            rows=[]
            for variant in ('before', 'after'):
                if variant == 'after':
                    run(['git', 'apply', '--unidiff-zero', str(HERE/'pilot.patch')], cwd=tree)
                # Detach any restored output hard links before Lake rebuilds the support file.
                for suffix in ('.olean', '.ilean', '.olean.private', '.olean.server'):
                    (tree/'.lake/build/lib/lean'/Path(SUPPORT).with_suffix(suffix)).unlink(missing_ok=True)
                (tree/'.lake/build/ir'/Path(SUPPORT).with_suffix('.c')).unlink(missing_ok=True)
                with (out/f'{variant}-support-build.log').open('w') as log:
                    run(['lake', 'build', 'Solidity.TestSuite.ScopedProblems'], cwd=tree, env=env, stdout=log, stderr=subprocess.STDOUT)
                with (out/f'{variant}-restore.log').open('w') as log:
                    run(['python3', 'scripts/ci/restore-lake-artifacts.py'], cwd=tree, env=env, stdout=log, stderr=subprocess.STDOUT)
                for repeat in range(a.repeats):
                    for p in [SUPPORT] + FILES:
                        stem=f'{variant}-{repeat}-{Path(p).stem}'
                        timing=out/f'{stem}.time'
                        # Run the file directly against restored imports, with no setup inside the timer.
                        # Unlink a restored hard link before overwriting a cached artifact.
                        olean=tree/'.lake/build/lib/lean'/Path(p).with_suffix('.olean')
                        olean.parent.mkdir(parents=True, exist_ok=True)
                        olean.unlink(missing_ok=True)
                        cmd=['lake', 'env', 'lean', p, '--tstack=131072', '-j1', '-o', str(olean)]
                        with (out/f'{stem}.log').open('w') as log:
                            start=time.perf_counter()
                            with subprocess.Popen(cmd, cwd=tree, env=env, stdout=log, stderr=subprocess.STDOUT) as proc:
                                _, status, usage=os.wait4(proc.pid, 0)
                                proc.returncode=os.waitstatus_to_exitcode(status)
                                if proc.returncode:
                                    raise subprocess.CalledProcessError(proc.returncode, cmd)
                            seconds=time.perf_counter()-start
                        kib=usage.ru_maxrss
                        timing.write_text(f'{seconds:.6f} {kib}\n')
                        rows.append(dict(variant=variant,repeat=repeat,file=p,seconds=float(seconds),peak_kib=int(kib),command=cmd))
                # Every original name must inhabit its original sequent; print transitive axioms too.
                audit='import Lean\n'+'\n'.join('import '+p[:-5].replace('/','.') for p in FILES)
                audit+='\nopen Solidity\nopen scoped Scoped\n'
                for ns in names.values():
                    for n in ns:
                        audit+=f'example : ⊢ {n}.problem := {n}.proved\n#print axioms {n}.proved\n'
                targets=', '.join('`'+p[:-5].replace('/', '.') for p in [SUPPORT]+FILES)
                audit+='run_cmd do\n  let env ← Lean.getEnv\n  for target in #['+targets+'] do\n'
                audit+='    let cs := env.constants.toList.filter fun (name, _) => (env.getModuleIdxFor? name).any (fun idx => env.header.moduleNames[idx.toNat]! == target)\n'
                audit+='    let ts := cs.filter fun (_, ci) => match ci with | .thmInfo _ => true | _ => false\n'
                audit+='    Lean.logInfo m!"PILOT_DECL {target} {cs.length} {ts.length}"\n'
                (tree/'PilotAudit.lean').write_text(audit)
                with (out/f'{variant}-meaning.log').open('w') as log:
                    run(['lake', 'env', 'lean', 'PilotAudit.lean', '--tstack=131072', '-j1'], cwd=tree, env=env, stdout=log, stderr=subprocess.STDOUT)
                text=(out/f'{variant}-meaning.log').read_text()
                reports = re.findall(r"^'(Solkey\.TestSuite\.\w+\.proved)' (?:depends on axioms|does not depend on any axioms)", text, re.M)
                assert 'sorryAx' not in text and set(reports) == {n+'.proved' for ns in names.values() for n in ns} and len(reports) == result['names'], 'incomplete axiom reports'
            result['runs']=rows
            # Compare all public transitive axiom reports, not just source spelling.
            b=(out/'before-meaning.log').read_text();c=(out/'after-meaning.log').read_text()
            def axiom_sets(text):
                reports=re.findall(r"^'(Solkey\.TestSuite\.\w+\.proved)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.M)
                return {n: sorted(x.strip() for x in axioms.split(',') if x.strip()) for n,axioms in reports}
            assert len(axiom_sets(b)) == result['names'] and axiom_sets(b) == axiom_sets(c), 'axiom reports changed'
            result['kernel_declarations']={v: [dict(module=m,constants=int(n),theorems=int(t)) for m,n,t in re.findall(r'PILOT_DECL (\S+) (\d+) (\d+)', (out/f'{v}-meaning.log').read_text())] for v in ('before','after')}
            assert all(len(result['kernel_declarations'][v]) == len(FILES)+1 for v in ('before','after'))
            result['meaning']='all original sequents kernel checked; identical transitive axiom reports'
            result['summary']=summarize(result)
        (out/'measurement.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
