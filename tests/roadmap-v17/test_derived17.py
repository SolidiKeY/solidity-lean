"""Supplemental wire controls; synthetic acceptance is never kernel evidence."""
import copy,importlib.util,json,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
s=importlib.util.spec_from_file_location('d',ROOT/'scripts/roadmap-v17-derived17.py');d=importlib.util.module_from_spec(s);s.loader.exec_module(d)
class DerivedControls(unittest.TestCase):
 def test_fixed_request_and_generic_refusal(self):
  good={'schema':1,'declarations':d.REQUESTS};self.assertEqual(d.fixed_request(good),good)
  for change in [('schema',True),('declarations',d.REQUESTS[:-1]),('declarations',d.REQUESTS[::-1])]:
   bad=copy.deepcopy(good);bad[change[0]]=change[1]
   with self.assertRaises(ValueError):d.fixed_request(bad)
  with self.assertRaises(ValueError):d.k.request({'schema':1,'module':'Solidity.TestSuite.Derived17','declarations':[{'name':d.REQUESTS[0]['name'],'kind':'theorem'}]})
 def value(self):
  rows=[]
  for wanted in d.REQUESTS:
   # Synthetic wire shape only: never a declaration or kernel witness.
   row=dict(wanted,nameAst=d.k.name_ast(wanted['name']),unsafe=False,partial=False,levels=[],type=['const',d.k.name_ast('True'),[]],value=['const',d.k.name_ast('True.intro'),[]],typeDisplaySupplemental='synthetic parser fixture only',typeDependencies=['True'],valueDependencies=['True.intro'],axioms=d.PINS,binderCount=0,propositionBinders=[],semanticPremisesDischarged=False);rows.append(row)
  return {'schema':1,'rows':rows,'imports':[],'releaseClosed':False}
 def raw(self,value):
  return ('V17_DERIVED_IDENTITIES_BEGIN\n'+json.dumps(d.REQUESTS)+'\nV17_DERIVED_IDENTITIES_END\nV17_KERNEL_BEGIN\n'+json.dumps(value)+'\nV17_KERNEL_END\n'+''.join("'"+r['name']+"' depends on axioms: [Classical.choice, Quot.sound, propext]\n" for r in value['rows'])).encode()
 def test_wire_baseline_and_rejections(self):
  value=self.value();self.assertEqual(d.metadata(self.raw(value)),value)
  changes=[('name','Solkey.TestSuite.fake.proved'),('module','Solidity.TestSuite.Derived17'),('kind','definition'),('axioms',[]),('type',None),('value',None),('type',['app']),('value',['bvar','0']),('typeDependencies',[]),('valueDependencies',[]),('semanticPremisesDischarged',True)]
  for key,v in changes:
   bad=copy.deepcopy(value);bad['rows'][0][key]=v
   with self.subTest(key=key),self.assertRaises((ValueError,KeyError,TypeError)):d.metadata(self.raw(bad))
  for key in ['value','type','typeDependencies','valueDependencies']:
   bad=copy.deepcopy(value);bad['rows'][0].pop(key)
   with self.assertRaises((ValueError,KeyError)):d.metadata(self.raw(bad))
  for bad in [self.raw(value)[:-25],self.raw(value)+b'V17_KERNEL_END\n',b'V17_DERIVED_IDENTITIES_BEGIN\n[]\nV17_DERIVED_IDENTITIES_END\n']:
   with self.assertRaises((ValueError,KeyError)):d.metadata(bad)
 def test_replay_rejects_coherent_forgery_and_inputs(self):
  value=self.value();self.assertTrue(d.exact_replay(value,value,{'source':'same'},{'source':'same'}))
  changed=copy.deepcopy(value);changed['rows'][0]['value']=['sort',['zero']];changed['rows'][0]['valueDependencies']=[]
  # Structurally consistent claims can pass wire checks; independent live output must match.
  self.assertEqual(d.metadata(self.raw(changed)),changed)
  with self.assertRaises(ValueError):d.exact_replay(value,changed,{}, {})
  with self.assertRaises(ValueError):d.exact_replay(value,value,{'setup':'real'},{'setup':'forged'})
 def test_no_budget_or_value_omission(self):
  q=d.query_bytes().decode();prefix=d.k.TEMPLATE.read_text().replace('-- V17_PROJECT_IMPORTS','import Solidity.TestSuite.Derived17');self.assertTrue(q.startswith(prefix));body=q[len(prefix):];self.assertIn('KernelQuery.extract #[',body);self.assertNotIn('includeValues',body);self.assertNotIn('valueOmitted',body)
  self.assertEqual(q.count('let result ←'),1)

class SupplementalInputControls(unittest.TestCase):
 """Actual retained input data, mocked corruption; no current proof claim."""
 @classmethod
 def setUpClass(cls):
  cls.producer=d.PRODUCER_ROOT;cls.current=d.e.load(cls.producer/'scoped-axioms/receipt/provenance.json')['before']
  cls.bound=d.inputs(cls.producer,cls.current)
 def changed_load(self,rel,mutate):
  from unittest.mock import patch
  original=d.e.load;target=self.producer/rel
  def load(path):
   value=original(path)
   if Path(path)==target:value=copy.deepcopy(value);mutate(value)
   return value
  return patch.object(d.e,'load',side_effect=load)
 def test_actual_bound_inputs_and_corrupt_reports(self):
  from unittest.mock import patch
  self.assertEqual(len(self.bound['actualProjectObjects']),250)
  cases=[('scoped-axioms/receipt/provenance.json',lambda x:x['before'].__setitem__('revision','f'*40)),('scoped-axioms/receipt/provenance.json',lambda x:x['budgets'].__setitem__('processSeconds',301)),('scoped-axioms/receipt/provenance.json',lambda x:x.__setitem__('commandExit',124)),('scoped-axioms/request.json',lambda x:x.__setitem__('inputValidationExit',125)),('scoped-axioms/verified.json',lambda x:x.__setitem__('actualSetupSha256','f'*64)),('scoped-axioms/verified.json',lambda x:x['names'].pop())]
  for rel,mutate in cases:
   with self.subTest(rel=rel),self.changed_load(rel,mutate),patch.object(d.k,'tool_inputs',return_value=self.bound['installedInputs']),self.assertRaises((ValueError,KeyError,OSError)):d.inputs(self.producer,self.current)
 def test_manifest_tool_source_and_object_corruption(self):
  from unittest.mock import patch
  original=d.p.resources.hash_file;manifest=self.producer/'SHA256SUMS';obj=Path(next(iter(self.bound['actualProjectObjects'].values()))['path'])
  for path in [manifest,obj]:
   with self.subTest(path=path),patch.object(d.p.resources,'hash_file',side_effect=lambda p: 'f'*64 if Path(p)==path else original(p)),patch.object(d.k,'tool_inputs',return_value=self.bound['installedInputs']),self.assertRaises(ValueError):d.inputs(self.producer,self.current)
  bad=copy.deepcopy(self.current);bad['runtime']['lean']['sha256']='f'*64
  with self.assertRaises(ValueError):d.inputs(self.producer,bad)
  bad=copy.deepcopy(self.bound['sourceClosure']);next(iter(bad['modules'].values()))['sha256']='f'*64
  with patch.object(d.k,'source_closure',return_value=bad),patch.object(d.k,'tool_inputs',return_value=self.bound['installedInputs']),self.assertRaises(ValueError):d.inputs(self.producer,self.current)
  bad=copy.deepcopy(self.bound['sourceClosure']);bad['modules'].pop(next(iter(bad['modules'])))
  with patch.object(d.k,'source_closure',return_value=bad),patch.object(d.k,'tool_inputs',return_value=self.bound['installedInputs']),self.assertRaises(ValueError):d.inputs(self.producer,self.current)
 def test_shell_and_completed_command_validation_phases(self):
  import tempfile
  with tempfile.TemporaryDirectory() as tmp:
   out=Path(tmp);(out/'run.sh').write_bytes(d.shell_bytes(out)+b'echo forged\n')
   with self.assertRaises(ValueError):d.validate_files(out,{}, {})
  raw={'exit':0,'commandExit':0,'executionExit':0,'cleanupExit':0,'validationExit':0}
  value=d.failure_outcome('validation',True,0,raw)
  self.assertEqual(value['collectorExit'],0);self.assertEqual(value['validationExit'],125);self.assertIsNone(value['collectionExceptionExit']);self.assertEqual(value['rawRecordOutcomes']['commandExit'],0)
  value=d.failure_outcome('collection',False,None,None);self.assertEqual(value['collectionExceptionExit'],2);self.assertIsNone(value['collectorExit']);self.assertIsNone(value['validationExit'])
