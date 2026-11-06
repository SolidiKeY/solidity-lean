import importlib.util,pathlib,unittest
p=pathlib.Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-yul/resources.py"
spec=importlib.util.spec_from_file_location("resources",p);r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
class Available(unittest.TestCase):
    def test_clean_cache_is_reclaimable(self):
        s=r.availability(16,13,5,3,0,0,10)
        self.assertEqual(s["raw_headroom_bytes"],3)
        self.assertEqual(s["available_estimate_bytes"],8)
    def test_dirty_writeback_not_counted(self):
        self.assertEqual(r.availability(16,13,5,3,1,1,10)["available_estimate_bytes"],6)
    def test_host_limit_applies(self):
        self.assertEqual(r.availability(16,10,5,3,0,0,2)["available_estimate_bytes"],2)
    def test_counter_clamps(self):
        self.assertEqual(r.availability(16,18,1,9,0,0,20)["available_estimate_bytes"],0)
        self.assertEqual(r.availability(16,10,1,9,3,0,20)["available_estimate_bytes"],6)
    def test_shmem_locked_and_watermark_excluded(self):
        s=r.availability(16,13,5,3,0,0,10,shmem=1,unevictable=1,host_low=2)
        self.assertEqual(s['clean_file_estimate_bytes'],3)
        self.assertEqual(s['cache_allowance_bytes'],1)
        self.assertEqual(s['available_estimate_bytes'],5)
    def test_inactive_metric_retained(self):
        s=r.availability(16,13,5,3,0,0,10)
        self.assertEqual(s['inactive_only_estimate_bytes'],6)
        self.assertEqual(s['available_estimate_bytes'],8)
    def test_invalid_counters_fail(self):
        with self.assertRaises(ValueError):r.availability(0,0,0,0,0,0,0)
        with self.assertRaises(ValueError):r.availability(16,-1,0,0,0,0,0)
if __name__=="__main__":unittest.main()
