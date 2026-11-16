#!/usr/bin/env python3
"""Real native fixtures: typed refs, quoted names, generated checks and async.
Use writer lock; serial pinned Lean. --check verifies small committed results.
"""
import argparse,hashlib,json,os,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent
SOURCE="""import Lean
set_option Elab.async false
namespace RawFixture
def target : Nat := 7
def localArg (F : Nat) : Nat := F
def withWhere (F : Nat) : Nat := helper F
where helper (n : Nat) : Nat := n
def asName : Lean.Name := ``RawFixture.target
def literalOnly : Lean.Name := `RawFixture.notAConstant
def stringOnly : String := "RawFixture.target"
#eval (``RawFixture.target).toString
example : RawFixture.target = 7 := rfl
macro "generated_check" : command => `(example : RawFixture.target = 7 := rfl)
generated_check
#check RawFixture.target in example : True := by trivial
run_cmd do
  Lean.Elab.Command.logSnapshotTask (.finished none { element := { desc := "fixture", diagnostics := .empty }, children := #[] })
end RawFixture
"""

def measure():
 cache=HERE.parents[3]/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 with tempfile.TemporaryDirectory(prefix='declgraph-rawref-fixture-',dir=cache) as directory:
  d=pathlib.Path(directory);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1');(d/'Fixture.lean').write_text(SOURCE)
  def run(args,good=True):
   result=subprocess.run(args,cwd=d,env=env,text=True,capture_output=True,timeout=120)
   if good:assert result.returncode==0,result.stdout+result.stderr
   return result
  run(['lean','--tstack=131072','-j1','-M10000','--root='+str(d),'-o','Fixture.olean','-i','Fixture.ilean','Fixture.lean'])
  modules=d/'modules.txt';modules.write_text('Fixture\n');native=d/'locals.jsonl'
  run(['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'LocalExport.lean'),str(modules),str(native)])
  constants=[json.loads(line) for line in native.read_text().splitlines() if json.loads(line)['record']=='constant']
  name_ci=next(row for row in constants if row['name']=='RawFixture.asName');assert 'RawFixture.target' not in name_ci['refs'],name_ci
  out=d/'raw.jsonl';result=run(['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'RawRefs.lean'),'Fixture.lean','Fixture',str(out)])
  assert 'RAW_REFS_CAPTURE_PASS' in result.stdout,result.stdout
  rows=[json.loads(line) for line in out.read_text().splitlines()];refs=[r for r in rows if r['record']=='identifier'];commands=[r for r in rows if r['record']=='command'];changes=[r for r in rows if r['record']=='coalescing_change']
  assert commands and all(r['unresolved_info_holes']==0 for r in commands)
  target=[r for r in refs if r['ident']['kind']=='const' and r['ident']['name']=='RawFixture.target' and not r['is_binder']]
  assert any(r['parent_decl']=='RawFixture.asName' for r in target),'Missing resolved quoted declaration name'
  assert not any(r['parent_decl'] in ('RawFixture.literalOnly','RawFixture.stringOnly') for r in target)
  assert not any(r['ident']['kind']=='const' and r['ident']['name']=='RawFixture.notAConstant' for r in refs)
  locals=[r for r in refs if r['parent_decl']=='RawFixture.localArg' and r['ident']['kind']=='fvar'];assert locals and any(not r['is_binder'] for r in locals)
  assert any(r['check_kind']=='eval' for r in target)
  example_commands={r['command'] for r in target if r['check_kind']=='example'};assert len(example_commands)==2,example_commands
  assert any(r['parent_decl'] in ('_check','RawFixture._check') and r['check_kind'] is None for r in target),'Prefix reference misattributed to trailing example'
  assert sum(r['finished_diagnostic_snapshots'] for r in commands)>=1,'Finished diagnostic snapshot not consumed'
  assert all(r['name_key'] is not None for r in refs)
  (d/'Async.lean').write_text('import Lean\nset_option Elab.async true\ntheorem delayed : True := by trivial\n');rejected=run(['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'RawRefs.lean'),'Async.lean','Async',str(d/'bad.jsonl')],good=False)
  assert rejected.returncode==2 and 'RAW_REFS_UNSUPPORTED' in rejected.stderr,rejected.stdout+rejected.stderr
  (d/'ErrorSnapshot.lean').write_text('import Lean\nrun_cmd do\n  let message : Lean.Message := { fileName := "ErrorSnapshot.lean", pos := { line := 2, column := 0 }, severity := .error, data := m!"snapshot fixture failure" }\n  let messages := ({} : Lean.MessageLog).add message\n  let diagnostics ← Lean.Language.Snapshot.Diagnostics.ofMessageLog messages\n  Lean.Elab.Command.logSnapshotTask (.finished none { element := { desc := "fixture_error", diagnostics }, children := #[] })\n')
  failed=run(['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'RawRefs.lean'),'ErrorSnapshot.lean','ErrorSnapshot',str(d/'error.jsonl')],good=False)
  assert failed.returncode==1 and 'snapshot fixture failure' in failed.stdout+failed.stderr,failed.stdout+failed.stderr
  error_body=(d/'ErrorSnapshot.lean').read_text().split('\n',1)[1]
  (d/'GuardedSnapshot.lean').write_text('import Lean\n/-- error: snapshot fixture failure -/\n#guard_msgs in\n'+error_body)
  guarded=run(['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'RawRefs.lean'),'GuardedSnapshot.lean','GuardedSnapshot',str(d/'guarded.jsonl')])
  assert 'RAW_REFS_CAPTURE_PASS' in guarded.stdout,guarded.stdout+guarded.stderr
  return dict(guarded_snapshot_error_consumed=True,snapshot_errors_preserved=True,prefix_reference_not_attributed_to_example=True,finished_diagnostic_snapshots_consumed=True,lean=version,producer_sha256=hashlib.sha256((HERE/'RawRefs.lean').read_bytes()).hexdigest(),source_sha256=hashlib.sha256(SOURCE.encode()).hexdigest(),native_identifier_events=len(refs),native_original_identifier_events=sum(r['origin']=='original' for r in refs),generated_or_other_origin_identifier_events=sum(r['origin']!='original' for r in refs),coalescing_changes=len(changes),local_variable_events=len(locals),resolved_quote_missing_from_kernel_refs_observed=True,literal_and_string_names_not_inferred=True,actual_example_command_events=len(example_commands),async_false_allowed=True,async_true_rejected=True,boundaries=['Observed native identifier-classifier events only; not exhaustive dependency or runtime tracing.', 'Reference identity is scoped to the captured context; event multiplicity and ancestry tags are not unique successful checks or roots.', 'Constants and fvars remain distinct; module hints name the first imported owner, not the selected proof-body origin.', 'Native coalescing is diagnostic only, using original references plus actual alias leaves; never used as graph edges.', 'Generated-origin events and typed name keys are retained separately; no lexical inference supplies use edges.'])

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();body=json.dumps(measure(),indent=2,sort_keys=True)+'\n';target=HERE/'raw-ref-fixtures.json';assert len(body.encode())<1000000
 if a.check:assert target.read_text()==body,'STALE raw-reference fixtures'
 else:target.write_text(body)
 print('RAW_REFERENCE_FIXTURES_PASS const_fvar_separation resolved_quotes no_literal_guess generated_checks async_guards')
if __name__=='__main__':main()
