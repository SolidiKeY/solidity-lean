"""Negative controls for migration admission and header discovery; no Lean server."""
import copy, importlib.util, sys, tempfile, unittest
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[4]
def load(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/"scripts/h62/item6/migrate-calculus"/(name+".py"))
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module); return module
census=load("census"); bounded=load("bounded"); cache=load("cache"); interfaces=load("interfaces")
class Tooling(unittest.TestCase):
    def test_nested_comment_and_module_header(self):
        self.assertEqual(census.header_imports("/- x /- import False -/ -/\nmodule\npublic import Solidity.Calculus.Fml -- comment\nmeta import Lean.Meta.Tactic.Assert\nnamespace N\nimport NotAHeader"),["Solidity.Calculus.Fml","Lean.Meta.Tactic.Assert"])
    def test_apostrophe_import(self):
        self.assertEqual(census.header_imports("import Loom.MonadAlgebras.WP.DoNames'\n"),["Loom.MonadAlgebras.WP.DoNames'"])
    def test_bad_import_is_not_silently_accepted(self):
        with self.assertRaises(ValueError): census.header_imports("import Foo; malicious")
    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError): census.header_imports("/- unfinished")
    def test_frozen_stream_truncation_rejected(self):
        interfaces.require_complete_count(47965,47965)
        with self.assertRaises(RuntimeError):interfaces.require_complete_count(47965,47964)
    def test_cache_advice_preserves_bytes_and_skips_symlinks(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder); data=root/"owned";data.write_bytes(b"preserve exact bytes")
            (root/"link").symlink_to(data)
            result=cache.advise_roots([root])
            self.assertEqual(result["files"],1)
            self.assertEqual(data.read_bytes(),b"preserve exact bytes")
            self.assertTrue((root/"link").is_symlink())
    def test_zombie_lean_does_not_count_as_live_worker(self):
        snapshot="PID PPID RSS STAT COMMAND COMMAND\n10 1 100 S lean lean -j1 file.lean\n11 1 0 Z lean [lean] <defunct>"
        self.assertEqual(bounded.observe_processes(snapshot),102400)
    def test_two_live_lean_workers_rejected(self):
        with self.assertRaises(RuntimeError): bounded.observe_processes("PID PPID RSS STAT COMMAND COMMAND\n10 1 100 S lean lean -j1 a.lean\n11 1 100 R lean lean -j1 b.lean")
    def test_missing_j1_rejected(self):
        with self.assertRaises(RuntimeError): bounded.observe_processes("PID PPID RSS STAT COMMAND COMMAND\n10 1 100 S lean lean a.lean")
    def test_stale_or_truncated_inventory_rejected(self):
        full=dict(closure_sources=[dict(path="x",sha256="abc",base_sha256="abc")])
        bounded.validate_inventory(full,copy.deepcopy(full),True)
        with self.assertRaises(RuntimeError): bounded.validate_inventory(dict(closure_sources=[]),full,False)
        changed=copy.deepcopy(full); changed["closure_sources"][0]["sha256"]="changed"
        with self.assertRaises(RuntimeError): bounded.validate_inventory(changed,changed,True)
if __name__=="__main__": unittest.main()
