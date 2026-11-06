import copy, importlib.util, pathlib, unittest
path=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul/compare.py'
spec=importlib.util.spec_from_file_location('compare',path);c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
class Comparison(unittest.TestCase):
    def reports(self):
        r=dict(status='pass',clean=True,kind='yul',census_sha256='x',resources={'cpu.max':'400000 100000'},swap_total_kib=0,reserve_bytes=4,sampled_rss_budget_bytes=12,guard_interval_seconds=.25,driver_sha256='x',resource_helper_sha256='r',resource_policy='v2',target_order_sha256='a',config_policy_sha256='b',source_check_before={'status':'pass'},source_check_after={'status':'pass'},modules=[{'module':'A','exit':0}],wall_seconds=100,peak_process_group_rss_bytes=100)
        return r,copy.deepcopy(r)
    def test_any_regression_escalates(self):
        a,b=self.reports(); b['wall_seconds']=101
        self.assertEqual(c.compare(a,b)['status'],'ESCALATE_REGRESSION')
    def test_exact_ten_escalates(self):
        a,b=self.reports();b['wall_seconds']=110;b['peak_process_group_rss_bytes']=110
        self.assertEqual(c.compare(a,b)['status'],'ESCALATE_REGRESSION')
    def test_rss_over_ten_stops(self):
        a,b=self.reports(); b['peak_process_group_rss_bytes']=111
        self.assertEqual(c.compare(a,b)['status'],'STOP_GT_10_PERCENT')
    def test_incomplete_rejected(self):
        a,b=self.reports();b['status']='running'
        with self.assertRaises(ValueError):c.compare(a,b)
    def test_resource_drift_rejected(self):
        a,b=self.reports();b['resources']['cpu.max']='max'
        with self.assertRaises(ValueError):c.compare(a,b)
    def test_nonfinite_rejected(self):
        a,b=self.reports();b['wall_seconds']=float('nan')
        with self.assertRaises(ValueError):c.compare(a,b)
    def test_source_revision_allowed(self):
        a,b=self.reports();b['census_sha256']='new-source'
        self.assertEqual(c.compare(a,b)['status'],'pass')
    def test_improvement_passes(self):
        a,b=self.reports();b['wall_seconds']=90
        self.assertEqual(c.compare(a,b)['status'],'pass')
if __name__=='__main__':unittest.main()
