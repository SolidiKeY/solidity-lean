"""Negative controls for migration admission and header discovery; no Lean server."""
import copy, importlib.util, sys, unittest
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[4]
def load(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/"scripts/h62/item6/migrate-calculus"/(name+".py"))
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module); return module
census=load("census"); bounded=load("bounded")
class Tooling(unittest.TestCase):
    def test_nested_comment_and_module_header(self):
        self.assertEqual(census.header_imports("/- x /- import False -/ -/\nmodule\npublic import Solidity.Calculus.Fml -- comment\nmeta import Lean.Meta.Tactic.Assert\nnamespace N\nimport NotAHeader"),["Solidity.Calculus.Fml","Lean.Meta.Tactic.Assert"])
    def test_apostrophe_import(self):
        self.assertEqual(census.header_imports("import Loom.MonadAlgebras.WP.DoNames'\n"),["Loom.MonadAlgebras.WP.DoNames'"])
    def test_bad_import_is_not_silently_accepted(self):
        with self.assertRaises(ValueError): census.header_imports("import Foo; malicious")
    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError): census.header_imports("/- unfinished")
    def test_stale_or_truncated_inventory_rejected(self):
        full=dict(closure_sources=[dict(path="x",sha256="abc",base_sha256="abc")])
        bounded.validate_inventory(full,copy.deepcopy(full),True)
        with self.assertRaises(RuntimeError): bounded.validate_inventory(dict(closure_sources=[]),full,False)
        changed=copy.deepcopy(full); changed["closure_sources"][0]["sha256"]="changed"
        with self.assertRaises(RuntimeError): bounded.validate_inventory(changed,changed,True)
if __name__=="__main__": unittest.main()
