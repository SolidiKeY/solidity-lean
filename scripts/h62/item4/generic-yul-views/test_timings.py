import copy
import unittest
from compare_timings import compare, PIN

class TimingControls(unittest.TestCase):
    def record(self):
        return dict(schema_version=1,conditions=dict(toolchain_archive_sha256=PIN,cache_state_sha256="a"*64,resource_policy_sha256="b"*64,original_case_inventory_sha256="c"*64,frozen_statement_inventory_sha256="d"*64,lean_threads=1,heavy_jobs=1,lean_args=["-j1"]),modules=["ReadControls"],trials=[dict(exit=0,resource_stop=None,wall_seconds=100,module_seconds=dict(ReadControls=100)) for _ in range(3)])
    def test_ten_percent_boundary_and_stop(self):
        a=self.record();b=copy.deepcopy(a)
        for t in b["trials"]:t.update(wall_seconds=110,module_seconds=dict(ReadControls=110))
        self.assertEqual(compare(a,b)["status"],"RECORDED_TIMING_ACCEPTANCE_PASS")
        b["trials"][0]["wall_seconds"]=111;b["trials"][1]["wall_seconds"]=111
        self.assertEqual(compare(a,b)["status"],"TIMING_STOP")
    def test_changed_cache_refused(self):
        a=self.record();b=copy.deepcopy(a);b["conditions"]["cache_state_sha256"]="e"*64
        with self.assertRaises(ValueError):compare(a,b)
    def test_failed_or_incomplete_run_refused(self):
        a=self.record()
        for mutate in (lambda b:b["trials"][0].update(exit=1),lambda b:b["trials"][0].update(resource_stop="memory"),lambda b:b["trials"][0].update(module_seconds={})):
            b=copy.deepcopy(a);mutate(b)
            with self.assertRaises(ValueError):compare(a,b)
    def test_added_helper_counted_in_aggregate(self):
        a=self.record();b=copy.deepcopy(a);b["modules"].append("GenericByteObjects")
        for t in b["trials"]:t["module_seconds"]["GenericByteObjects"]=11;t["wall_seconds"]=111
        self.assertEqual(compare(a,b)["status"],"TIMING_STOP")
    def test_module_name_cannot_overwrite_aggregate_stop(self):
        a=self.record();a["modules"]=["aggregate"]
        for t in a["trials"]:t["module_seconds"]={"aggregate":100}
        b=copy.deepcopy(a)
        for t in b["trials"]:t["wall_seconds"]=120
        r=compare(a,b)
        self.assertEqual(r["status"],"TIMING_STOP")
        self.assertTrue(r["rows"]["aggregate"]["stop"])
        self.assertFalse(r["rows"]["module:aggregate"]["stop"])
    def test_serial_metadata_refuses_overrides_and_wrong_types(self):
        # Guard recorded serial acceptance against conflicting CLI options and
        # Python's bool/int equality; these records do not establish a run.
        for args in (["-j1", "-j8"], ["-j1", "-j", "8"],
                     ["-j1", "--threads=8"], ["-j1", "--threads", "8"],
                     ["-j1", "-j1"], "-j1", ["-j1", 8], []):
            with self.subTest(args=args):
                a = self.record(); a["conditions"]["lean_args"] = args
                with self.assertRaises(ValueError): compare(a, a)
        for key in ("lean_threads", "heavy_jobs"):
            for value in (True, 1.0, "1", 2, None):
                with self.subTest(key=key, value=value):
                    a = self.record(); a["conditions"][key] = value
                    with self.assertRaises(ValueError): compare(a, a)
    def test_serial_metadata_keeps_non_thread_arguments(self):
        a = self.record(); a["conditions"]["lean_args"] += ["--tstack=131072"]
        self.assertEqual(compare(a,a)["status"], "RECORDED_TIMING_ACCEPTANCE_PASS")
    def test_nonfinite_timing_refused(self):
        a=self.record();b=copy.deepcopy(a);b["trials"][0]["wall_seconds"]="NaN"
        with self.assertRaises(ValueError):compare(a,b)

if __name__=="__main__":unittest.main()
