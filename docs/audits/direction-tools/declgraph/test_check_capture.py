#!/usr/bin/env python3
"""Real Lean fixtures for discarded example/eval and macro-generated contexts.
Use the writer lock; pinned Lean on PATH; heavy work serial. --check verifies the
small committed result. This does not measure repository-wide check roots.
"""
import argparse,hashlib,json,os,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent

def measure():
 root=HERE.parents[3];cache=root/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 version=subprocess.check_output(['lean','--version'],text=True).strip()
 assert 'version 4.24.0,' in version and '797c613' in version
 with tempfile.TemporaryDirectory(prefix='declgraph-check-fixture-',dir=cache) as directory:
  d=pathlib.Path(directory);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1')
  (d/'Support.lean').write_text('import Lean\ndef auditSupport : Nat := 7\n')
  (d/'Fixture.lean').write_text('import Support\ndef localSupport : Nat := auditSupport + 1\nexample : localSupport = 8 := rfl\nexample : auditSupport = 7 := rfl\n#eval localSupport\nmacro "generated_check" : command => `(example : localSupport = 8 := rfl)\ngenerated_check\n')
  def run(args):
   result=subprocess.run(args,cwd=d,env=env,text=True,capture_output=True,timeout=60);assert result.returncode==0,result.stdout+result.stderr;return result.stdout
  run(['lean','-j1','-M10000','-o','Support.olean','-i','Support.ilean','Support.lean'])
  out=d/'events.jsonl';stdout=run(['lean','-j1','-M10000','--run',str(HERE/'CheckExport.lean'),'Fixture.lean','Fixture',str(out)])
  assert 'CHECK_CONTEXT_CAPTURE_PASS' in stdout,stdout
  rows=[json.loads(line) for line in out.read_text().splitlines()]
  assert rows and not any(r.get('unresolved_info_hole') for r in rows),rows
  assert all(r['name'] not in ('localSupport','auditSupport') for r in rows),rows
  examples={r['command'] for r in rows if r['name']=='_example'};evaluations={r['command'] for r in rows if r['name']=='_eval'}
  assert len(examples)==3 and len(evaluations)==1,(examples,evaluations)
  assert any(r['name']=='_example' and r['syntax_kind']!='Lean.Parser.Command.declaration' for r in rows),rows
  assert any(n=='auditSupport' and owner=='Support' for r in rows for n,owner in zip(r['refs'],r['first_import_owner_hints']))
  assert any(n=='localSupport' and owner is None for r in rows for n,owner in zip(r['refs'],r['first_import_owner_hints']))
  (d/'Async.lean').write_text('import Support\nset_option Elab.async true\ntheorem delayed : True := by trivial\n')
  rejected=subprocess.run(['lean','-j1','-M10000','--run',str(HERE/'CheckExport.lean'),'Async.lean','Async',str(d/'async.jsonl')],cwd=d,env=env,text=True,capture_output=True,timeout=60)
  assert rejected.returncode==2 and 'CHECK_CONTEXT_CAPTURE_UNSUPPORTED' in rejected.stderr,rejected.stdout+rejected.stderr
  assert all(len(r['refs'])==len(r['first_import_owner_hints']) for r in rows)
  return dict(lean=version,producer_sha256=hashlib.sha256((HERE/'CheckExport.lean').read_bytes()).hexdigest(),example_command_events=len(examples),eval_command_events=len(evaluations),raw_saved_context_rows=len(rows),async_reenable_rejected=True,macro_generated_example_observed=True,imported_owner_observed=True,local_owner_absent_as_expected=True,boundaries=['Fixture events only; no repository-wide root or liveness census.', 'Raw contexts repeat declarations and include intermediate environments; rows are not distinct root counts.', 'A null import owner can denote a current-module or temporary declaration; it does not mean unused.', 'Saved contexts sample environments; declarations absent from all saved contexts are not observed. Context IDs are traversal order, not creation chronology.', 'Explicit async-option setters are rejected before elaboration; macro-created setters remain outside completeness claims.', 'Exclusion is post-command name presence; same-name transient versions may be omitted. Imported owners are first-owner hints, not resolved winners.', 'Enabled async or pending snapshot/lazy tasks are rejected; this raw capture does not certify arbitrary command effects.', 'Guarded failures, extension effects and runtime name construction require separate treatment.'])

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();body=json.dumps(measure(),indent=2,sort_keys=True)+'\n';target=HERE/'check-capture-fixtures.json'
 if a.check:assert target.read_text()==body,'STALE check fixtures'
 else:target.write_text(body)
 print('CHECK_CAPTURE_FIXTURES_PASS explicit_examples eval macro_generated_check imported_and_local_references')
if __name__=='__main__':main()
