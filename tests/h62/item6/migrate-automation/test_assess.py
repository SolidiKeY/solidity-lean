import importlib.util,pathlib,unittest
p=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-automation/assess.py'
s=importlib.util.spec_from_file_location('assess',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def receipt(wall=100,rss=100):
 return dict(command=['lake','--no-cache','build','Automation'],exit=0,guard_stop=None,wall_seconds=wall,sampled_peak_group_rss_bytes=rss,
 LEAN_NUM_THREADS='1',per_process_address_space_cap_bytes=12,aggregate_rss_guard_bytes=11,
 reserve_bytes=4,sample_interval_seconds=.05,headroom_basis='min(host,cgroup)',cgroup_memory_max='16',swap_total_bytes=0)
class CompareTests(unittest.TestCase):
 def test_failed_build_never_compared(self):
  self.assertIsNone(m.compare({'exit':0},{'exit':1})['wall_delta_percent'])
 def test_regression_escalates(self):
  self.assertEqual(m.compare(receipt(),receipt(wall=102))['status'],'escalate')
 def test_over_ten_percent_stops(self):
  self.assertEqual(m.compare(receipt(),receipt(wall=111))['status'],'STOP')
 def test_missing_resource_data_never_compared(self):
  x=receipt();x.pop('reserve_bytes')
  self.assertIsNone(m.compare(x,receipt())['wall_delta_percent'])
 def test_nan_never_compared(self):
  self.assertIsNone(m.compare(receipt(),receipt(wall=float('nan')))['wall_delta_percent'])
 def test_zero_never_compared(self):
  self.assertIsNone(m.compare(receipt(wall=0),receipt())['wall_delta_percent'])
 def test_target_mismatch_never_compared(self):
  other=receipt();other['command']=['lake','build','Other']
  self.assertIsNone(m.compare(receipt(),other)['wall_delta_percent'])
 def test_stop_propagates_despite_failed_acceptance(self):
  self.assertEqual(m.overall_status({'status':'STOP'},False),'STOP')
 def test_comparison_blocker_propagates(self):
  self.assertEqual(m.overall_status({'status':'blocked'},True),'blocked')
 def test_absent_guard_status_never_compared(self):
  x=receipt();x.pop('guard_stop')
  self.assertIsNone(m.compare(x,receipt())['wall_delta_percent'])
 def test_null_resource_never_compared(self):
  x=receipt();x['reserve_bytes']=None
  self.assertIsNone(m.compare(x,x)['wall_delta_percent'])
 def test_resource_mismatch_never_compared(self):
  self.assertIsNone(m.compare({'exit':0,'reserve_bytes':1},{'exit':0,'reserve_bytes':2})['wall_delta_percent'])
if __name__=='__main__':unittest.main()
