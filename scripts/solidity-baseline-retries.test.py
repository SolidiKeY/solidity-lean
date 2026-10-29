import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location('retries',Path(__file__).with_name('solidity-baseline-retries.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class Selection(unittest.TestCase):
 def row(self,path,failed):
  return {'path':path,'requiredPipelines':['legacy','viaIR'],'variants':[{'pipeline':p,**({'tool':{'timedOut':True}} if failed else {'status':'working'})} for p in ['legacy','viaIR']]}
 def test_first_resource_case_retained_and_followers_selected_once(self):
  rows=[self.row('a',False),self.row('b',True),self.row('c',True)]
  result=m.select({'metadata':{'batchSize':6},'results':rows},{'files':[{'path':p} for p in 'abc']})
  self.assertEqual(result['fixtures'],['c']);self.assertEqual(result['queuedModeJobs'],6)
 def test_unattempted_nonruntime_assets_not_added(self):
  rows=[self.row('a',False),{'path':'b','status':'blocked'}]
  result=m.select({'metadata':{'batchSize':16},'results':rows},{'files':[{'path':p} for p in 'abc']})
  self.assertEqual(result['fixtures'],[]);self.assertEqual(result['queuedModeJobs'],2)
 def test_first_case_in_any_batch_is_never_a_follower_retry(self):
  rows=[self.row('a',True),self.row('b',True)]
  result=m.select({'metadata':{'batchSize':3},'results':rows},{'files':[{'path':p} for p in 'ab']})
  self.assertEqual(result['fixtures'],[])
 def test_observation_prefix_must_not_shrink_or_change(self):
  old={'variants':[{'pipeline':'legacy','observed':[{'value':1},{'value':2}]}]}
  equal={'variants':[{'pipeline':'legacy','observed':[{'value':1},{'value':2}]}]}
  longer={'variants':[{'pipeline':'legacy','observed':[{'value':1},{'value':2},{'value':3}]}]}
  short={'variants':[{'pipeline':'legacy','observed':[{'value':1}]}]}
  changed={'variants':[{'pipeline':'legacy','observed':[{'value':4},{'value':2}]}]}
  self.assertTrue(m.observations_preserved(old,equal));self.assertTrue(m.observations_preserved(old,longer))
  self.assertFalse(m.observations_preserved(old,short));self.assertFalse(m.observations_preserved(old,changed))
 def test_duplicate_mode_is_rejected(self):
  row=self.row('a',False);row['variants'].append(row['variants'][0])
  with self.assertRaisesRegex(ValueError,'duplicate pipeline'):m.select({'metadata':{'batchSize':16},'results':[row]},{'files':[{'path':'a'}]})
if __name__=='__main__':unittest.main()
