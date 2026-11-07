"""Acceptance controls: incomplete, wrong-toolchain and regressed runs fail closed."""
import copy, importlib.util, pathlib, unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
s=importlib.util.spec_from_file_location("compare",ROOT/"scripts/h62/item6/migrate-typing/compare.py")
c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
def result(new=False):
    v,commit,short=c.VERSIONS["new" if new else "old"]
    hashes={"Module"+str(i):"a"*64 for i in range(64)}
    return {"versions":{"lean":f"Lean (version {v}, x86_64-unknown-linux-gnu, commit {commit}, Release)","lake":f"Lake version 5.0.0-src+{short} (Lean version {v})"},"passed":True,"records":[{"module":m,"source_sha256":h,"exit":0,"resource_stop":None} for m,h in hashes.items()],"planned_modules":64,"source_drift":False,"settings":{},"provenance":{**{k:0 for k in c.RESOURCE_FIELDS},"all_closure_sources_equal_base":True},"closure_source_sha256":hashes,"wall_seconds":100.,"peak_aggregate_rss_bytes":100.}
class Controls(unittest.TestCase):
    def check(self,alter,status):
        a=result();b=result(True);alter(b)
        self.assertEqual(c.compare(a,b)["status"],status)
    def test_failed_build(self):self.check(lambda b:b.update(passed=False),"INCOMPARABLE")
    def test_resource_mismatch(self):self.check(lambda b:b["provenance"].update(cpu_max=4),"INCOMPARABLE")
    def test_regression_stop(self):self.check(lambda b:b.update(wall_seconds=111),"STOP_GT_10_PERCENT")
    def test_exact_ten_percent(self):self.check(lambda b:b.update(wall_seconds=110),"REGRESSION_ESCALATE")
    def test_small_regression_escalates(self):self.check(lambda b:b.update(wall_seconds=101),"REGRESSION_ESCALATE")
    def test_improvement(self):self.check(lambda b:b.update(wall_seconds=90,peak_aggregate_rss_bytes=90),"PASS")
    def test_old_as_new(self):self.assertEqual(c.compare(result(),result())["status"],"INCOMPARABLE")
    def test_duplicate_modules(self):self.check(lambda b:b.update(records=[b["records"][0]]*64),"INCOMPARABLE")
    def test_record_hash_mismatch(self):self.check(lambda b:b["records"][0].update(source_sha256="b"*64),"INCOMPARABLE")
    def test_nan(self):self.check(lambda b:b.update(wall_seconds=float("nan")),"INCOMPARABLE")
    def test_null_exit(self):self.check(lambda b:b["records"][0].update(exit=None),"INCOMPARABLE")
    def test_zero(self):self.check(lambda b:b.update(wall_seconds=0),"INCOMPARABLE")
    def test_fixture_mode(self):self.check(lambda b:b.update(fixture="fixture.lean"),"INCOMPARABLE")
    def test_cached_import_mode(self):self.check(lambda b:b.update(imports="old/lib"),"INCOMPARABLE")
if __name__=="__main__":unittest.main()
