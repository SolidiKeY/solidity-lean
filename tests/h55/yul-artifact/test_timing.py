import importlib.util, pathlib, unittest
root=pathlib.Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('timing',root/'scripts/h55/yul-artifact/compare_timing.py')
timing=importlib.util.module_from_spec(spec); spec.loader.exec_module(timing)
def record(seconds):
    return dict(command=['lean','-j1','same.lean'],address_space_limit_bytes=12*1024**3,
        reserve_bytes=4*1024**3,lean_num_threads=1,swap_configured=False,
        toolchain='fixture',executor='fixture',cache_state='fixture',exit_code=0,
        stop_reason=None,wall_seconds=seconds)
class TimingTests(unittest.TestCase):
    def test_strict_ten_percent_boundary(self):
        self.assertFalse(timing.compare([record(10)],[record(11)])['stop'])
        self.assertTrue(timing.compare([record(10)],[record('11.0001')])['stop'])
    def test_changed_or_missing_conditions_refused(self):
        changed=record(10); changed['command']=['lean','different.lean']
        with self.assertRaises(ValueError): timing.compare([record(10)],[changed])
        del changed['toolchain']
        with self.assertRaises(ValueError): timing.compare([record(10)],[changed])
    def test_failed_or_stopped_run_refused(self):
        failed=record(10); failed['exit_code']=137
        with self.assertRaises(ValueError): timing.compare([record(10)],[failed])
    def test_incomplete_metadata_refused(self):
        bad=record(10); del bad['stop_reason']
        with self.assertRaises(ValueError): timing.compare([bad],[bad])
        for key,value in [('command',[]),('toolchain',None),('executor',''),('cache_state',None),('address_space_limit_bytes',None),('reserve_bytes',0)]:
            bad=record(10); bad[key]=value
            with self.assertRaises(ValueError): timing.compare([bad],[bad])

    def test_one_slow_pair_is_not_hidden(self):
        self.assertTrue(timing.compare([record(10),record(10)],[record(1),record(12)])['stop'])
if __name__ == '__main__': unittest.main()
