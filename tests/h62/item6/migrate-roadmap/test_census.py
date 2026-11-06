"""Source census controls. These tests make no Lean compatibility claim."""
import importlib.util, pathlib, sys, unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("census",ROOT/"scripts/h62/item6/migrate-roadmap/census.py")
census=importlib.util.module_from_spec(spec);spec.loader.exec_module(census)
spec=importlib.util.spec_from_file_location("graph",ROOT/"scripts/v08-build-graph.py")
graph=importlib.util.module_from_spec(spec);spec.loader.exec_module(graph)
class CensusControls(unittest.TestCase):
    def test_nested_comments_and_multiple_imports(self):
        self.assertEqual(graph.header_imports("/- import Fake /- nested -/ -/\nimport A B -- comment"),["A","B"])
    def test_qualifiers(self):
        self.assertEqual(graph.header_imports("public meta import Lean\nmeta import Std"),["Lean","Std"])
    def test_prelude(self):
        self.assertEqual(graph.header_imports("-- import Fake\nprelude\nimport Init"),["Init"])
    def test_invalid_name_rejected(self):
        with self.assertRaises(ValueError):graph.header_imports("import Invalid-Name")
    def test_body_not_an_import(self):
        self.assertEqual(graph.header_imports('def x := "import Fake"\nimport Ignored'),[])
    def test_empty(self):self.assertEqual(graph.header_imports(""),[])
    def test_exporter_import_coverage(self):
        c=census.census(ROOT)
        imports=graph.header_imports((ROOT/"tests/h62/item6/migrate-roadmap/ExportAll.lean").read_text())
        self.assertEqual(set(imports)-{"Lean"},set(c["targets"]))
        imports=graph.header_imports((ROOT/"tests/h62/item6/migrate-roadmap/ExportEvm.lean").read_text())
        self.assertEqual(set(imports),{"Lean","Solidity.Roadmap.Evm"})
    def test_full_assigned_census_and_order(self):
        c=census.census(ROOT)
        self.assertEqual(c,census.census(ROOT))
        self.assertEqual(len(c["targets"]),15)
        self.assertTrue(all(m["unchanged"] for m in c["modules"]))
        positions={m:i for i,m in enumerate(c["closure"])}
        g=census.graph(ROOT)
        for m in c["closure"]:
            for d in g.imports(m):
                if g.source(d):self.assertLess(positions[d],positions[m],(m,d))
if __name__=="__main__":unittest.main()
