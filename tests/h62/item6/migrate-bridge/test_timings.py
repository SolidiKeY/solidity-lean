"""Negative controls for measurement acceptance; fixtures are synthetic, not Lean runs."""
import importlib.util,json,pathlib,subprocess,sys,tempfile,unittest
p=pathlib.Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-bridge/compare-timings.py"
spec=importlib.util.spec_from_file_location("timings",p); timing=importlib.util.module_from_spec(spec); spec.loader.exec_module(timing)
class TimingControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup); self.root=pathlib.Path(self.tmp.name)
        self.old=self.root/"old"; self.new=self.root/"new"; self.old.mkdir(); self.new.mkdir()
        self.write(self.old,"4.24.0",100); self.write(self.new,"4.35.0",100)
    def write(self,path,version,elapsed,**changes):
        data={"status":"command-pass","exit":0,"resource_stop":None,"elapsed_seconds":elapsed,
              "versions":{"lean":"Lean (version "+version+", fixture)","lake":"Lake fixture (Lean version "+version+")"},
              "command":["bash","./run-lean.sh","--bridge"],"measurement_scope":"full-root-and-Bridge","build_tree_policy":"Lean library outputs cold; prebuilt ProofWidgets JS only","compiler_args":["-j1","-M10240"],"module_timeout_seconds":300,"reserve_gib":4,"swap_bytes":0,"cache":"disabled via empty LAKE_CACHE_DIR and --no-cache","solkey_rules_sha256":"f"*64}
        data.update(changes); (path/"receipt.json").write_text(json.dumps(data))
    def test_equal_and_faster(self):
        self.assertEqual(timing.compare(self.old,self.new)["action"],"no-regression")
        self.write(self.new,"4.35.0",90); self.assertEqual(timing.compare(self.old,self.new)["action"],"no-regression")
    def test_ten_percent_boundary_requires_escalation(self):
        self.write(self.new,"4.35.0",110); self.assertEqual(timing.compare(self.old,self.new)["action"],"escalate")
    def test_above_ten_percent_stops(self):
        self.write(self.new,"4.35.0",110.001); self.assertEqual(timing.compare(self.old,self.new)["action"],"stop")
    def test_interrupted_run_rejected(self):
        self.write(self.old,"4.24.0",81,status="fail",exit=-15)
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_mismatched_resources_rejected(self):
        self.write(self.new,"4.35.0",90,compiler_args=["-j1","-M3072"])
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_pending_watchdog_rejected(self):
        (self.old/"active-attempt-runner.py").write_text("fixture")
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_watchdog_resource_stop_rejected(self):
        (self.old/"active-attempt-runner.py").write_text("fixture")
        (self.old/"cgroup-watchdog.json").write_text(json.dumps({"reserve_gib":4,"resource_stop":"low headroom"}))
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_zero_and_nonfinite_times_rejected(self):
        for value in (0,-1,"NaN","Infinity",True):
            self.write(self.new,"4.35.0",value)
            with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_missing_receipt_rejected(self):
        (self.new/"receipt.json").unlink()
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_missing_resource_stop_rejected(self):
        data=json.loads((self.old/"receipt.json").read_text()); del data["resource_stop"]
        (self.old/"receipt.json").write_text(json.dumps(data))
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_equal_invalid_profiles_rejected(self):
        for changes in ({"compiler_args":[]},{"reserve_gib":0},{"swap_bytes":1},{"command":None},{"module_timeout_seconds":True},{"build_tree_policy":"warm Lean outputs"}):
            self.write(self.old,"4.24.0",100,**changes); self.write(self.new,"4.35.0",100,**changes)
            with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_incomplete_watchdog_rejected(self):
        (self.old/"active-attempt-runner.py").write_text("fixture")
        (self.old/"cgroup-watchdog.json").write_text(json.dumps({"reserve_gib":4}))
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_valid_watchdog_accepted(self):
        (self.old/"active-attempt-runner.py").write_text("fixture")
        (self.old/"cgroup-watchdog.json").write_text(json.dumps({"reserve_gib":4,"resource_stop":None,"elapsed_seconds":99,"watched_pgid":123,"peak_vm_cgroup_bytes":100}))
        self.assertEqual(timing.compare(self.old,self.new)["action"],"no-regression")
    def test_exact_above_threshold_not_rounded_to_ten(self):
        self.write(self.new,"4.35.0","110.0000000000000000000000000000000001")
        self.assertEqual(timing.compare(self.old,self.new)["action"],"stop")
    def test_cli_stop_and_malformed_object_are_typed(self):
        cli=[sys.executable,str(p),"--old",str(self.old),"--new",str(self.new)]
        self.write(self.new,"4.35.0",111)
        proc=subprocess.run(cli,capture_output=True,text=True); self.assertEqual(proc.returncode,4); self.assertEqual(json.loads(proc.stdout)["action"],"stop")
        for malformed in ([],None):
            (self.new/"receipt.json").write_text(json.dumps(malformed))
            proc=subprocess.run(cli,capture_output=True,text=True); self.assertEqual(proc.returncode,2); self.assertEqual(json.loads(proc.stdout)["action"],"blocked")
    def test_bridge_measurement_scope(self):
        for path,version in ((self.old,"4.24.0"),(self.new,"4.35.0")):
            self.write(path,version,100,command=["bash","./scripts/check-bridge.sh"],measurement_scope="Bridge")
        result=timing.compare(self.old,self.new)
        self.assertEqual(result["action"],"no-regression"); self.assertEqual(result["measurement_scope"],"Bridge"); self.assertEqual(result["command"],["bash","./scripts/check-bridge.sh"])
    def test_cross_scope_comparison_rejected(self):
        self.write(self.new,"4.35.0",100,command=["bash","./scripts/check-bridge.sh"],measurement_scope="Bridge")
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
    def test_wrong_scope_label_rejected(self):
        for path,version in ((self.old,"4.24.0"),(self.new,"4.35.0")):
            self.write(path,version,100,command=["bash","./scripts/check-bridge.sh"])
        with self.assertRaises(timing.Blocked): timing.compare(self.old,self.new)
if __name__=="__main__": unittest.main()
