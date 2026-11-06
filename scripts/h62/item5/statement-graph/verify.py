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
    resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3))


def error_diagnostics(log):
    """Read compiler error bodies only; never count filenames or warnings."""
    bodies = []
    for line in log.splitlines():
        try:
            message = json.loads(line)
        except ValueError:
            continue
        if isinstance(message,dict) and message.get('severity')=='error' and isinstance(message.get('data'),str):
            bodies.append(message['data'])
    return bodies


def has_error_diagnostic(log, expected):
    return any(body.strip()==expected for body in error_diagnostics(log))


def is_witness_conflict_diagnostic(log):
    helper = 'H62.CheckedWitness.H62Fixture.root.binder_1'
    return any(body.strip()=='conflicting imported H62 witnesses' or
               ('environment already contains' in body and helper in body)
               for body in error_diagnostics(log))


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
        run('fixture',[lean,*flags,'-o',str(build/SCOPE/'Fixture.olean'),str(SCOPE/'Fixture.lean')])
        original = (evidence/'fixture.json').read_bytes()
        exported = {r['declaration']:r for r in json.loads(original)['declarations']}
        assert [f['name'] for f in exported['H62Fixture.Certificate']['fields']] == ['resource','valid']
        assert exported['H62Fixture.useCertificate']['binders'][0]['isProp'] is False
        assert 'Lean.Expr.fvar' not in exported['H62Fixture.Certificate']['fields'][1]['typeExpr']
        census = (evidence/'fixture-census.json').read_bytes()
        assert census == (evidence/'fixture-census-repeat.json').read_bytes()
        census_rows = json.loads(census)['declarations']
        assert len(census_rows)>len(exported) and all('H62Fixture.' in r['declaration'] for r in census_rows)
        assert any(r['constantKind']=='constructor' for r in census_rows)
        assert any(r['declaration'].startswith('_private.') and r['declaration'].endswith('.H62Fixture.privateWitness') for r in census_rows)
        assert original == (evidence/'fixture-repeat.json').read_bytes(), 'same-process nondeterminism'
        run('fixture-fresh',[lean,*flags,str(SCOPE/'Fixture.lean')])
        assert original == (evidence/'fixture.json').read_bytes(), 'fresh-process nondeterminism'
        assert census == (evidence/'fixture-census.json').read_bytes(), 'fresh-process census nondeterminism'
        run('witness-fixture',[lean,*flags,'-o',str(build/SCOPE/'WitnessFixture.olean'),str(SCOPE/'WitnessFixture.lean')])
        witness_bytes = (evidence/'witness-fixture.json').read_bytes()
        witness_exports = {r['declaration']:r for r in json.loads(witness_bytes)['declarations']}
        assert not witness_exports['H62WitnessFixture.useCertificate']['binders'][0]['isProp']
        assert witness_exports['H62WitnessFixture.Certificate']['typeExpr'] == 'Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))'
        assert ' '.join(witness_exports['H62WitnessFixture.Pair']['typeExpr'].split()) == 'Lean.Expr.forallE `n (Lean.Expr.const `Nat []) (Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))) (Lean.BinderInfo.default)'
        assert witness_bytes == (evidence/'witness-fixture-repeat.json').read_bytes(), 'same-process witness nondeterminism'
        run('witness-fixture-fresh',[lean,*flags,str(SCOPE/'WitnessFixture.lean')])
        assert witness_bytes == (evidence/'witness-fixture.json').read_bytes(), 'fresh-process witness nondeterminism'
        # Each negative driver must fail for its intended witness check, not a setup error.
        witness_negatives = {
            'witness-wrong-type': ('#h62_witness "binder" H62WitnessFixture.naturalReflexive 0 H62WitnessFixture.trueProducer', 'H62 witness type does not match the exact universal premise closure'),
            'witness-wrong-index': ('#h62_witness "binder" H62WitnessFixture.consumer 99 H62WitnessFixture.naturalReflexive', 'H62 witness binder index is out of range'),
            'witness-unsafe': ('#h62_witness "binder" H62WitnessFixture.naturalReflexive 0 unsafeCast', 'unsafe H62 witness is forbidden'),
            'witness-axiom-dependent': ('#h62_witness "binder" H62WitnessFixture.naturalReflexive 0 Classical.choice', 'H62 witness must be axiom-free'),
            'witness-duplicate': ('#h62_witness "binder" H62WitnessFixture.consumer 1 H62WitnessFixture.naturalReflexive', 'duplicate H62 witness registration'),
            'witness-universe-specialization': ('universe v\ntheorem mono (α : Type) (x : α) : x = x := rfl\ntheorem broad (α : Type v) (x : α) (same : x = x) : x = x := same\n#h62_witness "binder" broad 2 mono', 'H62 witness type does not match the exact universal premise closure')
        }
        witness_negatives.update({
            'witness-kernel-skip': ('set_option debug.skipKernelTC true in\n#h62_witness "binder" H62WitnessFixture.naturalReflexive 0 H62WitnessFixture.trueProducer', 'H62 witness requires kernel checking'),
            'witness-unresolved-universe': ("""run_cmd Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
  name := `phantom
  levelParams := [`v]
  type := Lean.mkConst ``True
  value := Lean.mkConst ``True.intro
  hints := .opaque
  safety := .safe }
theorem need (h : True) : True := h
#h62_witness "binder" need 0 phantom""", 'H62 witness is not closed or has unresolved metavariables')})
        for label,(body,expected_text) in witness_negatives.items():
            driver = evidence/(label+'.lean')
            driver.write_text('import tests.h62.item5.«statement-graph».WitnessFixture\n/-! Guard regression: '+label+' must be refused by the H62 exporter. -/\n'+body+'\n')
            run(label,[lean,*flags,'--json',str(driver)],expected=1)
            assert has_error_diagnostic((evidence/(label+'.log')).read_text(), expected_text), 'wrong negative-control failure: '+label
        for label,producer in (('WitnessOverlayA','H62Fixture.leaf'),('WitnessOverlayB','H62Fixture.reflexive')):
            driver = evidence/(label+'.lean')
            driver.write_text('import tests.h62.item5.«statement-graph».Fixture\n#h62_witness "binder" H62Fixture.root 1 '+producer+'\n')
            run(label,[lean,*flags,'-R',str(evidence),'-o',str(build/(label+'.olean')),str(driver)])
        conflict = evidence/'witness-overlay-conflict.lean'
        conflict.write_text('import WitnessOverlayA\nimport WitnessOverlayB\n#h62_export "negative-imported-witness.json" [H62Fixture.root]\n')
        run('witness-overlay-conflict',[lean,*flags,'--json',str(conflict)],expected=1)
        failure = (evidence/'witness-overlay-conflict.log').read_text()
        assert is_witness_conflict_diagnostic(failure), 'wrong imported-witness failure'
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
        run('pending-export',[lean,*flags,str(SCOPE/'Pending.lean')])
        run('python-tests',[sys.executable,'-B',str(SCOPE/'test_graph.py')])
        tree = subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip()
        run('fixture-graph',[sys.executable,'-B','scripts/h62/item5/statement-graph/graph.py','build',
             '--export',str(evidence/'fixture.json'),'--catalog',str(SCOPE/'catalog.json'),
             '--base',BASE,'--tree',tree,'--output',str(evidence/'fixture-graph.json')])
        run('pending-graph',[sys.executable,'-B','scripts/h62/item5/statement-graph/graph.py','build',
             '--export',str(evidence/'pending-export.json'),'--catalog',str(SCOPE/'pending-inputs.json'),
             '--ownership','/workspace/h62-coordinator-inputs/ownership.json',
             '--base',BASE,'--tree',tree,'--output',str(evidence/'pending-graph.json')])
        pending = json.loads((evidence/'pending-graph.json').read_text())
        assert pending['counts']['blocked']==5 and pending['counts']['pendingInputs']==5
        assert pending['counts']['typedDeclarations']==0 and pending['counts']['openPremises'] is None
        assert not pending['counts']['premiseInventoryComplete']
        run('witness-graph',[sys.executable,'-B','scripts/h62/item5/statement-graph/graph.py','build',
             '--export',str(evidence/'witness-fixture.json'),'--catalog',str(SCOPE/'witness-catalog.json'),
             '--base',BASE,'--tree',tree,'--output',str(evidence/'witness-graph.json')])
        witness_graph = json.loads((evidence/'witness-graph.json').read_text())
        rows = {n['id']:n for n in witness_graph['nodes']}
        assert rows['consumer']['status']=='done' and rows['polyConsumer']['status']=='done'
        assert rows['Certificate']['status']!='done' and rows['useCertificate']['status']=='blocked'
        assert rows['useCertificate']['premises'][0]['status']=='done'
        assert [p['status'] for p in rows['Pair']['premises']]==['done','done']
        assert rows['Pair']['status']!='done'
        assert rows['conditional']['status']=='blocked' and rows['conditional']['controlRole']=='intentional-contradiction'
        assert rows['conditional']['premises'][1]['blockedByPremises']==['conditional#0']
        assert witness_graph['progress']['positiveWitness']['openPremises']==0
        assert witness_graph['progress']['intentionalContradiction']['openPremises']==2
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
