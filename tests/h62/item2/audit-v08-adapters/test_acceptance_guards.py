"""Acceptance and frozen-baseline regression tests; never proof evidence."""
import ast,hashlib,importlib.util,json,pathlib,subprocess,sys,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
SCRIPTS=ROOT/'scripts/h62/item2/audit-v08-adapters'
sys.path.insert(0,str(SCRIPTS))
spec=importlib.util.spec_from_file_location('accept_witnesses',SCRIPTS/'accept_witnesses.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
BASE='1506ee968e25a97aa63605301a651e33339a57c3'
class Guards(unittest.TestCase):
 def test_all_original_predicates_retained(self):
  total=0
  for name in ['accept_witnesses.py','accept_local_guard.py','h70_inventory.py']:
   path='scripts/h62/item2/audit-v08-adapters/'+name
   before=ast.parse(subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+path]).decode())
   after=ast.parse((ROOT/path).read_text())
   old=sorted((n for n in ast.walk(before) if isinstance(n,ast.Assert)),key=lambda n:n.lineno)
   new=sorted((n for n in ast.walk(after) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='require'),key=lambda n:n.lineno)
   self.assertFalse(any(isinstance(n,ast.Assert) for n in ast.walk(after)))
   self.assertEqual([ast.dump(n.test) for n in old],[ast.dump(n.args[0]) for n in new]);total+=len(old)
  self.assertEqual(total,44)
 def test_captured_run_predicates(self):
  # This is fake metadata solely for exercising acceptance checks.
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp)/'repo';root.mkdir();source=root/'fixture.txt';source.write_text('not a Lean proof')
   run=pathlib.Path(tmp)/'run';run.mkdir()
   good=dict(versions=['Lean (version 4.24.0, 797c613eb9b6d4ec95db23e3e00af9ac6657f24b)'],records=[dict(exit=0,stop=None)],no_swap=True,cap_bytes=12*1024**3,reserve_bytes=4*1024**3)
   def write(data,sha=None):
    (run/'results.json').write_text(json.dumps(data))
    (run/'source-sha256.json').write_text(json.dumps({'fixture.txt':sha or hashlib.sha256(source.read_bytes()).hexdigest()}))
   write(good);m.checked_run(root,run)
   bads=[{**good,'versions':['wrong toolchain']},{**good,'records':[dict(exit=1,stop=None)]},{**good,'records':[dict(exit=0,stop='STOP')]},{**good,'no_swap':False},{**good,'cap_bytes':0},{**good,'reserve_bytes':0},
    {**good,'versions':['Lean (version 4.24.0, wrong-commit)']},
    {**good,'records':[]},
    {**good,'records':[dict(exit=0,stop=None),dict(exit=1,stop=None)]},
    {**good,'records':[dict(exit=1,stop=None),dict(exit=0,stop=None)]},
    {**good,'records':[dict(exit=0,stop=None),dict(exit=0,stop='headroom')]},
    {**good,'records':[dict(exit=0,stop='timeout'),dict(exit=0,stop=None)]}]
   for bad in bads:
    with self.subTest(bad=bad):
     write(bad)
     with self.assertRaises(ValueError):m.checked_run(root,run)
   write(good,'0'*64)
   with self.assertRaises(ValueError):m.checked_run(root,run)
 def test_require_rejects_false(self):
  with self.assertRaises(ValueError):m.require(False,'metadata rejection')

class FrozenBaseline(unittest.TestCase):
 def test_exact_one_reviewed_override(self):
  spec=importlib.util.spec_from_file_location('audit_census',SCRIPTS/'census.py')
  c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
  frozen=c.frozen_blobs(ROOT)
  baseline={}
  for record in subprocess.check_output(['git','-C',str(ROOT),'ls-tree','-rz',c.BASE]).split(b'\0'):
   if record:
    metadata,path=record.split(b'\t',1);baseline[path.decode()]=metadata.split()[2].decode()
  path='Solidity/Backend/CalldataPackets/RawAddress/Controls.lean'
  self.assertEqual(set(c.BASELINE_OVERRIDES),{path})
  self.assertEqual({p for p in set(frozen)|set(baseline) if frozen.get(p)!=baseline.get(p)},{path})
  c.verify_frozen(ROOT,frozen,path)
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);target=root/path;target.parent.mkdir(parents=True)
   target.write_bytes((ROOT/path).read_bytes()+b'\n-- unreviewed drift\n')
   with self.assertRaises(SystemExit):c.verify_frozen(root,frozen,path)
   other='unapproved.lean';(root/other).write_text('unapproved')
   with self.assertRaises(SystemExit):c.verify_frozen(root,frozen,other)

unittest.main()
