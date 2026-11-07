#!/usr/bin/env python3
"""Negative controls for omitted scope and fabricated/failed acceptance evidence."""
import copy,importlib.util,json,pathlib,subprocess,tempfile,time,unittest
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('h28check',HERE/'check.py'); check=importlib.util.module_from_spec(spec); spec.loader.exec_module(check)
BASE=json.loads((HERE/'inventory.json').read_text())
class AccountingControls(unittest.TestCase):
 def resource_fixture(self):
  meta=json.loads((HERE/'evidence/memory-controls-kernel-02.json').read_text())
  return meta,json.loads((check.ROOT/meta['rusage_file']).read_text())
 def test_resource_fixture(self): self.assertEqual(check.resource_errors(*self.resource_fixture()),[])
 def test_parallel_lean_workers_rejected(self):
  meta,usage=self.resource_fixture();meta['worker_snapshots']=[['1024 lean -j1 a.lean','1024 /tool/bin/lean -j1 b.lean']]
  self.assertIn('multiple heavy Lean workers observed',check.resource_errors(meta,usage))
 def test_worker_argv0_forms(self):
  spec=importlib.util.spec_from_file_location('h28workers',HERE/'runtime/workers.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
  rows=['1024 lean -j1 a.lean','2048 /tool/bin/lean -j1 b.lean','4096 ./lean --deps c.lean']
  ps='\n'.join(rows+['32 ps -eo rss,args','64 python3 /bin/lean --not-a-worker','','1024'])
  self.assertEqual(module.lean_workers(ps),rows)
 def test_probe_shim_serializes_and_preserves_failure(self):
  # Controlled OS child only: no Lean/theorem output is mocked or accepted.
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory);fake=out/'controlled-child';shim=out/'lake';lock=out/'cold/locks/probe.lock'
   fake.write_text("#!/usr/bin/env python3\nimport json,pathlib,sys,time\np=pathlib.Path(sys.argv[4]);root=p.parent\nwith (root/'events').open('a') as f:f.write(json.dumps(['start',p.name,sys.argv[1:]])+'\\n')\np.touch()\nif p.name=='first':\n deadline=time.monotonic()+3\n while not (root/'release').exists() and time.monotonic()<deadline:time.sleep(.01)\nwith (root/'events').open('a') as f:f.write(json.dumps(['end',p.name])+'\\n')\nprint('CONTROLLED_RUNTIME_CHILD_NO_LEAN')\nsys.exit(23 if p.name=='fail' else 0)\n")
   fake.chmod(0o755)
   text=(HERE/'runtime/bin/lake').read_text().replace('real=/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','real='+str(fake)).replace('lock=/workspace/solidity-lean/tests/h28-sol/non-vacuity/runtime/build/corpus-probe.lock','lock='+str(lock))
   shim.write_text(text);shim.chmod(0o755)
   def command(name):return [str(shim),'--quiet','--no-build','lean',str(out/name),'--','--tstack=131072']
   first=subprocess.Popen(command('first'),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True);second=None
   try:
    deadline=time.monotonic()+2
    while not (out/'first').exists() and first.poll() is None and time.monotonic()<deadline:time.sleep(.01)
    self.assertTrue((out/'first').exists(),'controlled child did not start')
    self.assertEqual(subprocess.run(['flock','-n',str(lock),'true']).returncode,1,'shim did not hold lock across child')
    second=subprocess.Popen(command('second'),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    (out/'release').touch();first.communicate(timeout=3);second.communicate(timeout=3)
    self.assertEqual((first.returncode,second.returncode),(0,0))
    events=[json.loads(x) for x in (out/'events').read_text().splitlines()]
    self.assertEqual([(x[0],x[1]) for x in events],[('start','first'),('end','first'),('start','second'),('end','second')])
    self.assertTrue(all(x[2][-1]=='-j1' for x in events if x[0]=='start'))
    failed=subprocess.run(command('fail'),capture_output=True,text=True,timeout=3)
    self.assertEqual(failed.returncode,23);self.assertIn('CONTROLLED_RUNTIME_CHILD_NO_LEAN',failed.stdout)
   finally:
    (out/'release').touch()
    for child in [first,second]:
     if child is not None and child.poll() is None:child.kill();child.communicate()
 def test_missing_headroom_rejected(self):
  meta,usage=self.resource_fixture(); meta.pop('minimum_vm_available_bytes')
  self.assertTrue(check.resource_errors(meta,usage))
 def test_increased_oom_rejected(self):
  meta,usage=self.resource_fixture(); meta['final_memory_events']['oom_kill']+=1
  self.assertTrue(check.resource_errors(meta,usage))
 def test_missing_rusage_rejected(self):
  meta,_=self.resource_fixture(); self.assertTrue(check.resource_errors(meta,{}))
 def test_reclamation_cannot_hide_observed_breach(self):
  meta,usage=self.resource_fixture();meta['minimum_vm_available_bytes']=4*1024**3-1
  meta['cache_reclaims']=[{'after':{'available':8*1024**3}}]
  self.assertIn('estimated VM headroom below 4 GiB or missing',check.resource_errors(meta,usage))
 def changed(self,edit):
  d=copy.deepcopy(BASE); edit(d); return check.validate(d)
 def test_structural_inventory(self): self.assertEqual(check.validate(BASE),[])
 def test_changed_historical_adoption_rejected(self):
  self.assertTrue(self.changed(lambda d:d['integration_history'][-1].update(merge='0'*40)))
 def test_entered_turn_promotion_rejected(self):
  self.assertTrue(self.changed(lambda d:d['loop_backfill'].update(body_turns=1)))
 def test_omitted_loop_joint_witness_rejected(self):
  self.assertTrue(self.changed(lambda d:d['loop_backfill']['theorems'].pop()))
 def test_vm_shipping_policy_rejected(self):
  self.assertTrue(self.changed(lambda d:d['cache_handoff'].update(vm_ship_cache=True)))
 def test_omitted_adoption_history_rejected(self):
  self.assertTrue(self.changed(lambda d:d.pop('integration_history')))
 def test_changed_adoption_anchor_rejected(self):
  self.assertTrue(self.changed(lambda d:d['integration_adoption'].update(upstream='0'*40)))
 def test_omitted_public_theorem(self): self.assertTrue(self.changed(lambda d:d['theorems'].pop()))
 def test_signature_body_swallowed(self): self.assertTrue(self.changed(lambda d:d['theorems'][0]['original'].update(signature_source='wrong proof body')))
 def test_omitted_checked_branch(self): self.assertTrue(self.changed(lambda d:d['checked_branches'].pop()))
 def test_omitted_statement_constructor(self): self.assertTrue(self.changed(lambda d:d['constructor_families'][0]['constructors'].pop()))
 def test_omitted_family(self): self.assertTrue(self.changed(lambda d:d['constructor_families'].pop()))
 def test_changed_constructor_clause(self):
  self.assertTrue(self.changed(lambda d:d['constructor_families'][0]['constructors'][0].update(clause_source='omitted premise')))
 def test_changed_source_identity(self): self.assertTrue(self.changed(lambda d:d['sources'][0].update(sha256='0'*64)))
 def test_changed_base(self): self.assertTrue(self.changed(lambda d:d.update(base='0'*40)))
 def fabricated(self):
  d=copy.deepcopy(BASE)
  witness=[{'file':'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/Families.lean','name':'Solidity.Assurance.NonVacuityH28.closed_simulation'}]
  rows=d['theorems']+d['checked_branches']+d['controls']+[x for f in d['constructor_families'] for x in f['constructors']]
  for x in rows: x.update(status='witnessed',witnesses=witness)
  d['acceptance']='complete'; return d
 def test_original_status_stays_open(self):
  d=self.fabricated(); d['theorems'][0]['original']['status']='open'
  errors=check.validate(d,True)
  self.assertTrue(any(x.startswith('OPEN: original') for x in errors))
 def test_premise_status_stays_open(self):
  d=self.fabricated()
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   rows=json.loads((out/'premise-expansions.json').read_text());rows[0]['status']='open'
   (out/'premise-expansions.json').write_text(json.dumps(rows));errors=check.validate(d,True,out)
  self.assertTrue(any(x.startswith('OPEN: premise') for x in errors))
 def test_empty_evidence_cannot_promote_acceptance(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory)
   for name in ['registration.json','premise-expansions.json','signature-names.json','axiom-pins.json','open-premises.json','resource-findings.json','statement-analysis.json','public-contracts.json']:
    (out/name).write_bytes((HERE/name).read_bytes())
   for name in ['final-gates.json','final-reviews.json']:(out/name).write_text('{}')
   errors=check.validate(self.fabricated(),True,out)
   self.assertTrue(any('malformed or missing required evidence' in x for x in errors))
 def test_failed_gate_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory)
   for name in ['registration.json','premise-expansions.json','signature-names.json','axiom-pins.json','open-premises.json','resource-findings.json','statement-analysis.json','public-contracts.json']:(out/name).write_bytes((HERE/name).read_bytes())
   (out/'bad.log').write_text('Build completed successfully\n')
   (out/'bad.json').write_text(json.dumps({'exit':1,'stop':None,'limits':[str(12*1024**3),'0'],'command':['bash','run-lean.sh']}))
   row={'metadata':'bad.json','log':'bad.log','log_sha256':check.sha(out/'bad.log'),'command':['bash','run-lean.sh']}
   (out/'final-gates.json').write_text(json.dumps({'gates':{'full':row}}))
   errors=check.validate(self.fabricated(),True,out)
   self.assertIn('failed final gate: full',errors)
 def test_omitted_countercontrols(self): self.assertTrue(self.changed(lambda d:d.update(controls=[])))
 def temp_fixture(self,out):
  for name in ['registration.json','premise-expansions.json','signature-names.json','axiom-pins.json','open-premises.json','resource-findings.json','statement-analysis.json','public-contracts.json']:(out/name).write_bytes((HERE/name).read_bytes())
 def test_omitted_assert_dispatch_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory);self.temp_fixture(out)
   d=json.loads((out/'statement-analysis.json').read_text());d['constructors'].pop('assert')
   (out/'statement-analysis.json').write_text(json.dumps(d))
   self.assertIn('statement analysis inventory incomplete',check.validate(BASE,False,out))
 def test_omitted_open_finding_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   d=json.loads((out/'open-premises.json').read_text()); d['findings'].pop()
   (out/'open-premises.json').write_text(json.dumps(d))
   self.assertIn('open premise finding inventory incomplete or duplicated',check.validate(BASE,False,out))
 def test_open_finding_source_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   d=json.loads((out/'open-premises.json').read_text()); d['findings'][0]['clause_sha256']='0'*64
   (out/'open-premises.json').write_text(json.dumps(d))
   self.assertTrue(any('open premise finding source differs' in e for e in check.validate(BASE,False,out)))
 def test_omitted_resource_finding_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   d=json.loads((out/'resource-findings.json').read_text()); d['findings'].pop()
   (out/'resource-findings.json').write_text(json.dumps(d))
   self.assertIn('resource finding inventory incomplete or duplicated',check.validate(BASE,False,out))
 def test_resource_clause_cosubstitution_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   d=json.loads((out/'resource-findings.json').read_text()); first=d['findings'][0]
   d['findings']=[dict(first,id=x['id']) for x in d['findings']]
   (out/'resource-findings.json').write_text(json.dumps(d))
   self.assertTrue(any('resource finding ID/clause mapping differs' in e for e in check.validate(BASE,False,out)))
 def test_constructor_line_cosubstitution_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   d=copy.deepcopy(BASE); f=d['constructor_families'][0]; row=f['constructors'][0]; row['source_line']=1
   findings=json.loads((out/'open-premises.json').read_text())
   for x in findings['findings']:
    if x['id']=='H28-'+f['family'].upper()+'-'+row['name']: x['line']=1
   (out/'open-premises.json').write_text(json.dumps(findings))
   self.assertTrue(any('constructor source line differs' in e for e in check.validate(d,False,out)))
 def test_omitted_contract_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory);self.temp_fixture(out)
   rows=json.loads((out/'public-contracts.json').read_text());rows['contracts'].pop()
   (out/'public-contracts.json').write_text(json.dumps(rows))
   self.assertIn('delegated contract inventory incomplete or duplicated',check.validate(BASE,False,out))
 def test_contract_cosubstitution_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory);self.temp_fixture(out)
   rows=json.loads((out/'public-contracts.json').read_text());first=rows['contracts'][0]
   rows['contracts']=[dict(first,id=x['id']) for x in rows['contracts']]
   (out/'public-contracts.json').write_text(json.dumps(rows))
   self.assertTrue(any('delegated contract mapping differs' in e for e in check.validate(BASE,False,out)))
 def test_omitted_contract_field_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory);self.temp_fixture(out)
   rows=json.loads((out/'public-contracts.json').read_text())
   selected=next(x for x in rows['contracts'] if x['fields']);selected['fields'].pop()
   (out/'public-contracts.json').write_text(json.dumps(rows))
   self.assertTrue(any('delegated field/constructor inventory differs' in e for e in check.validate(BASE,False,out)))
 def test_generic_finding_not_accepted(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory);self.temp_fixture(out)
   rows=json.loads((out/'open-premises.json').read_text())
   rows['findings'][0]['missing_constructive_obligation']='No constructor-by-constructor coverage yet.'
   (out/'open-premises.json').write_text(json.dumps(rows))
   errors=check.validate(BASE,True,out)
   self.assertTrue(any('generic unfinished finding' in e for e in errors))
 def test_uninhabited_leaf_cannot_be_promoted(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory);self.temp_fixture(out)
   rows=json.loads((out/'public-contracts.json').read_text())
   row=next(x for x in rows['contracts'] if x['id']=='Solidity.Evm.Memory.FixedArrayRepr')
   row.update(status='witnessed',witnesses=[{'file':'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/Families.lean','name':'Solidity.Assurance.NonVacuityH28.closed_simulation'}],findings=[],boundary='All fixed arrays witnessed')
   (out/'public-contracts.json').write_text(json.dumps(rows))
   self.assertIn('delegated contract coverage policy differs: Solidity.Evm.Memory.FixedArrayRepr',check.validate(BASE,False,out))
 def test_empty_premise_slice_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   rows=json.loads((out/'premise-expansions.json').read_text()); rows[0]['text']=''
   (out/'premise-expansions.json').write_text(json.dumps(rows))
   self.assertIn('premise expansion empty or incomplete',check.validate(BASE,False,out))
 def test_duplicate_premise_slices_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   rows=json.loads((out/'premise-expansions.json').read_text())
   (out/'premise-expansions.json').write_text(json.dumps([rows[0]]*len(rows)))
   self.assertIn('premise expansion set incomplete or duplicated',check.validate(BASE,False,out))
 def test_pin_and_signature_coomission_rejected(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   names=json.loads((out/'signature-names.json').read_text()); removed=names.pop()
   pins=json.loads((out/'axiom-pins.json').read_text()); del pins['theorems'][removed]
   (out/'signature-names.json').write_text(json.dumps(names)); (out/'axiom-pins.json').write_text(json.dumps(pins))
   errors=check.validate(BASE,False,out)
   self.assertIn('kernel signature inventory incomplete',errors); self.assertIn('axiom pin inventory incomplete',errors)
 def test_review_identity_checked_per_area(self):
  with tempfile.TemporaryDirectory(dir=HERE) as directory:
   out=pathlib.Path(directory); self.temp_fixture(out)
   (out/'final-gates.json').write_text('{"gates":{}}'); (out/'reviewed-inputs.json').write_text(json.dumps({'sha256':check.review_input_hashes()})); (out/'review.txt').write_text('synthetic mutation control')
   reviews=[]
   for i,area in enumerate(sorted(check.AREAS)):
    for role in ['finder','skeptic']:reviews.append({'area':area,'role':role,'agent':'same-agent-'+str(i),'verdict':'pass','read_only':True,'used_lean_server':False,'artifact':'review.txt','sha256':check.sha(out/'review.txt')})
   (out/'final-reviews.json').write_text(json.dumps({'reviews':reviews}))
   errors=check.validate(self.fabricated(),True,out)
   self.assertTrue(any(x.startswith('finder/skeptic not independent for ') for x in errors))

 def test_completed_reverting_turn_promotion_rejected(self):
  self.assertTrue(any('entered revert scope differs' in x for x in self.changed(lambda d:d['entered_revert_backfill'].update(completed_body_turns=1))))
 def test_published_copy_anchor_mutation_rejected(self):
  self.assertTrue(any('published copy record differs' in x for x in self.changed(lambda d:d['published_copy'].update(upstream='0'*40))))

if __name__=='__main__': unittest.main()
