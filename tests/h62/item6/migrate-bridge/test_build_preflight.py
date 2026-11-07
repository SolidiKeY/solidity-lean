"""Cold-proof-output controls; JS assets are setup data, never Lean proof caches."""
import importlib.util,json,pathlib,tempfile,unittest
p=pathlib.Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-bridge/run-bounded.py"
spec=importlib.util.spec_from_file_location("bounded",p); bounded=importlib.util.module_from_spec(spec); spec.loader.exec_module(bounded)
class ColdBuildControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup); self.root=pathlib.Path(self.tmp.name)
    def make(self,name):
        p=self.root/name; p.mkdir(parents=True); return p
    def test_empty_is_cold(self): bounded.check_cold_build(self.root)
    def test_root_and_bridge_outputs_rejected(self):
        for name in (".lake/build","Bridge/.lake/build"):
            self.make(name)
            with self.assertRaises(ValueError): bounded.check_cold_build(self.root)
            (self.root/name).rmdir()
    def test_dependency_outputs_rejected(self):
        self.make("Bridge/.lake/packages/mathlib/.lake/build")
        with self.assertRaises(ValueError): bounded.check_cold_build(self.root)
    def test_only_prepared_widget_js_accepted(self):
        js=self.make("Bridge/.lake/packages/proofwidgets/.lake/build/js"); (js/"main.js").write_text("fixture")
        bounded.check_cold_build(self.root)
    def test_widget_lean_cache_rejected(self):
        self.make("Bridge/.lake/packages/proofwidgets/.lake/build/js")
        lib=self.make("Bridge/.lake/packages/proofwidgets/.lake/build/lib/lean"); (lib/"Foo.olean").write_text("fixture")
        with self.assertRaises(ValueError): bounded.check_cold_build(self.root)
    def test_disguised_lean_asset_rejected(self):
        js=self.make("Bridge/.lake/packages/proofwidgets/.lake/build/js")
        for name in ("Foo.olean","Foo.olean.private","Foo.olean.server","Foo.ilean.hash","Foo.ir","Foo.bc","Foo.c.hash","cache.bin"):
            artifact=js/name; artifact.write_text("fixture")
            with self.assertRaises(ValueError): bounded.check_cold_build(self.root)
            artifact.unlink()
    def test_symlinked_js_rejected(self):
        build=self.make("Bridge/.lake/packages/proofwidgets/.lake/build"); target=self.make("assets"); (build/"js").symlink_to(target)
        with self.assertRaises(ValueError): bounded.check_cold_build(self.root)
    def test_missing_js_fails_before_measurement(self):
        (self.root/"Bridge").mkdir(); (self.root/"Bridge/lake-manifest.json").write_text(json.dumps({"packages":[{"name":"proofwidgets"}]}))
        with self.assertRaises(ValueError): bounded.require_js_assets(self.root)
    def test_prepared_js_prerequisite(self):
        js=self.make("Bridge/.lake/packages/proofwidgets/.lake/build/js"); (js/"main.js").write_text("fixture"); (js/"lake.trace").write_text("fixture")
        (self.root/"Bridge/lake-manifest.json").write_text(json.dumps({"packages":[{"name":"proofwidgets"}]}))
        bounded.require_js_assets(self.root)
    def test_js_does_not_whitelist_other_dependency_builds(self):
        self.make("Bridge/.lake/packages/mathlib/.lake/build/js")
        with self.assertRaises(ValueError): bounded.check_cold_build(self.root)
if __name__=="__main__": unittest.main()
