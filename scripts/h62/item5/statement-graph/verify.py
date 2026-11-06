#!/usr/bin/env python3
"""Serial, pinned, bounded H62 acceptance. Bulk outputs stay in --evidence."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

if not __debug__:
    raise RuntimeError('H62 verification cannot run with Python optimization enabled')

ROOT = Path(__file__).resolve().parents[4]
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
SCOPE = Path('tests/h62/item5/statement-graph')


def sha(path):
    with Path(path).open('rb') as src:
        return hashlib.file_digest(src, 'sha256').hexdigest()


def available():
    values = dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
    reserve = int(values['MemAvailable'].split()[0])*1024
    cap = Path('/sys/fs/cgroup/memory.max')
    current = Path('/sys/fs/cgroup/memory.current')
    if cap.exists() and cap.read_text().strip() != 'max':
        reserve = min(reserve,int(cap.read_text())-int(current.read_text()))
    return reserve


def bounds():
    resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin',type=Path,required=True)
    parser.add_argument('--pin',type=Path,required=True)
    parser.add_argument('--archive',type=Path,required=True)
    parser.add_argument('--evidence',type=Path,required=True)
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    if evidence.is_relative_to(ROOT):
        parser.error('evidence must be outside the checkout')
    pin = json.loads(args.pin.read_text())
    assert sha(args.archive) == pin['sha256'], 'pinned archive checksum mismatch'
    assert not int(next(l for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('SwapTotal:')).split()[1]), 'swap must be disabled'
    lockpath = Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lockpath.parent.mkdir(parents=True,exist_ok=True)
    with lockpath.open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX | fcntl.LOCK_NB)
        evidence.mkdir(parents=True,exist_ok=True)
        build = evidence/'build'
        (build/SCOPE).mkdir(parents=True,exist_ok=True)
        env = dict(os.environ,PATH=str(args.lean_bin.resolve())+os.pathsep+os.environ['PATH'],
                   LEAN_NUM_THREADS='1',LEAN_PATH=str(build),H62_GRAPH_OUTPUT_DIR=str(evidence),PYTHONDONTWRITEBYTECODE='1')
        before_status = subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=ROOT,text=True)
        assert not before_status, 'acceptance requires clean committed sources: '+before_status
        source_head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        runs = []
        def run(label,cmd,expected=0):
            assert available() >= 4*1024**3, 'insufficient available-memory reserve'
            start = time.monotonic()
            with (evidence/(label+'.log')).open('w') as out:
                proc = subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT,
                                        start_new_session=True,preexec_fn=bounds)
                try:
                    while proc.poll() is None:
                        if time.monotonic()-start > 120 or available() < 4*1024**3:
                            raise RuntimeError('timeout or 4GiB reserve crossed')
                        time.sleep(.05)
                except BaseException:
                    os.killpg(proc.pid,signal.SIGKILL)
                    proc.wait()
                    raise
            result = dict(command=cmd,exit=proc.returncode,seconds=time.monotonic()-start,log=str(evidence/(label+'.log')))
            runs.append(result)
            (evidence/'commands.json').write_text(json.dumps(runs,indent=2)+'\n')
            assert proc.returncode == expected, result
            return result
        lean = str(args.lean_bin.resolve()/'lean')
        flags = ['-j1','--tstack=131072']
        run('lean-version',[lean,'--version'])
        run('lake-version',[str(args.lean_bin.resolve()/'lake'),'--version'])
        assert pin['toolchain'].split(':')[-1].lstrip('v') in (evidence/'lean-version.log').read_text()
        subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
        baseline = []
        candidate = []
        # Same source/cache/resources: core has no import of this optional tool.
        # Interleave identical core controls to expose drift rather than assert speedup.
        for i in range(7):
            baseline.append(run('keysort-before-'+str(i),[lean,*flags,'Solidity/KeySort.lean'])['seconds'])
        run('exporter',[lean,*flags,'-o',str(build/SCOPE/'Exporter.olean'),str(SCOPE/'Exporter.lean')])
        run('fixture',[lean,*flags,str(SCOPE/'Fixture.lean')])
        original = (evidence/'fixture.json').read_bytes()
        exported = {r['declaration']:r for r in json.loads(original)['declarations']}
        assert [f['name'] for f in exported['H62Fixture.Certificate']['fields']] == ['resource','valid']
        assert exported['H62Fixture.useCertificate']['binders'][0]['isProp'] is False
        assert 'Lean.Expr.fvar' not in exported['H62Fixture.Certificate']['fields'][1]['typeExpr']
        census = (evidence/'fixture-census.json').read_bytes()
        assert census == (evidence/'fixture-census-repeat.json').read_bytes()
        census_rows = json.loads(census)['declarations']
        assert len(census_rows)>len(exported) and all(r['declaration'].startswith('H62Fixture.') for r in census_rows)
        assert any(r['constantKind']=='constructor' for r in census_rows)
        assert original == (evidence/'fixture-repeat.json').read_bytes(), 'same-process nondeterminism'
        run('fixture-fresh',[lean,*flags,str(SCOPE/'Fixture.lean')])
        assert original == (evidence/'fixture.json').read_bytes(), 'fresh-process nondeterminism'
        assert census == (evidence/'fixture-census.json').read_bytes(), 'fresh-process census nondeterminism'
        # Unknown/dead declaration and conflicting roles must fail elaboration.
        for label,body in {
            'dead-declaration':'#h62_export "negative-dead.json" [H62Missing.declaration]',
            'duplicate-declaration':'#h62_export "negative-duplicate.json" [Nat, Nat]',
            'conflicting-tags':'@[h62_statement, h62_premise] def h62Conflict : Prop := True\n#h62_export "negative-tags.json" [h62Conflict]'
        }.items():
            driver = evidence/(label+'.lean')
            driver.write_text('import tests.h62.item5.«statement-graph».Exporter\n'+body+'\n')
            run(label,[lean,*flags,str(driver)],expected=1)
        for label,kind in (('OverlayA','statement'),('OverlayB','premise')):
            driver = evidence/(label+'.lean')
            driver.write_text('import tests.h62.item5.«statement-graph».Exporter\n#h62_tag "'+kind+'" Nat.add_comm\n')
            run(label,[lean,*flags,'-R',str(evidence),'-o',str(build/(label+'.olean')),str(driver)])
        conflict = evidence/'overlay-conflict.lean'
        conflict.write_text('import OverlayA\nimport OverlayB\n#h62_export "negative-overlay.json" [Nat.add_comm]\n')
        run('overlay-conflict',[lean,*flags,str(conflict)],expected=1)
        assert 'conflicting H62 tags' in (evidence/'overlay-conflict.log').read_text()
        assert not list(evidence.glob('negative-*.json')), 'negative export produced a snapshot'
        run('python-tests',[sys.executable,'-B',str(SCOPE/'test_graph.py')])
        tree = subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip()
        run('fixture-graph',[sys.executable,'-B','scripts/h62/item5/statement-graph/graph.py','build',
             '--export',str(evidence/'fixture.json'),'--catalog',str(SCOPE/'catalog.json'),
             '--base',BASE,'--tree',tree,'--output',str(evidence/'fixture-graph.json')])
        for i in range(7):
            candidate.append(run('keysort-after-'+str(i),[lean,*flags,'Solidity/KeySort.lean'])['seconds'])
        import statistics
        before,after = statistics.median(baseline),statistics.median(candidate)
        delta = after/before-1
        timings = dict(control='unchanged Solidity/KeySort.lean, pinned toolchain, seven serial warm runs',
                       before=baseline,after=candidate,beforeMedian=before,afterMedian=after,deltaPercent=100*delta,
                       thresholdPercent=10,pass_=delta<=.1)
        (evidence/'timings.json').write_text(json.dumps(timings,indent=2)+'\n')
        assert delta <= .1, 'STOP: control median slowed >10%; inspect timings.json'
        after_status = subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=ROOT,text=True)
        assert not after_status, 'source checkout changed during acceptance: '+after_status
        assert source_head == subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), 'HEAD changed during acceptance'
        provenance = dict(head=source_head,base=BASE,tree=tree,pinSha256=sha(args.pin),archiveSha256=sha(args.archive),
                          sourceSha256={str(p.relative_to(ROOT)):sha(p) for scope in ('tests/h62/item5/statement-graph','scripts/h62/item5/statement-graph') for p in sorted((ROOT/scope).rglob('*')) if p.is_file()})
        (evidence/'provenance.json').write_text(json.dumps(provenance,sort_keys=True,indent=2)+'\n')
        manifest = {str(p.relative_to(evidence)):sha(p) for p in sorted(evidence.rglob('*')) if p.is_file() and p.name!='sha256.json'}
        (evidence/'sha256.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
        print('H62_FIXTURE_ACCEPTANCE_PASS (does not establish production G49/G50 coverage or full runtime gate)')

if __name__ == '__main__':
    main()
