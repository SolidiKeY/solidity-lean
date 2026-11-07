"""Source census controls. These tests make no Lean compatibility claim."""
import importlib.util, pathlib, subprocess, sys, unittest
from unittest.mock import patch
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("census",ROOT/"scripts/h62/item6/migrate-roadmap/census.py")
census=importlib.util.module_from_spec(spec);spec.loader.exec_module(census)
spec=importlib.util.spec_from_file_location("graph",ROOT/"scripts/v08-build-graph.py")
graph=importlib.util.module_from_spec(spec);spec.loader.exec_module(graph)
spec=importlib.util.spec_from_file_location("bounded_build",ROOT/"scripts/h62/item6/migrate-roadmap/build.py")
bounded_build=importlib.util.module_from_spec(spec);spec.loader.exec_module(bounded_build)
class CensusControls(unittest.TestCase):
    def test_daemon_timeout_is_failed_observation(self):
        with patch.object(bounded_build.subprocess,"run",side_effect=subprocess.TimeoutExpired(["docker"],2)):
            result=bounded_build.bounded_control(["docker"],env={},text=True,stdout=subprocess.PIPE)
        self.assertEqual(result.returncode,124)
        self.assertEqual(result.stdout,"")
    def test_daemon_errors_remain_errors(self):
        failure=subprocess.CompletedProcess(["docker"],1,stdout="",stderr="not running")
        with patch.object(bounded_build.subprocess,"run",return_value=failure) as run:
            result=bounded_build.bounded_control(["docker"],env={},text=True)
        self.assertIs(result,failure)
        self.assertEqual(run.call_args.kwargs["timeout"],2)

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
    def test_new_producer_modules_do_not_expand_assignment(self):
        c=census.census(ROOT)
        assigned={m["path"] for m in c["modules"]}
        observed={str(p.relative_to(ROOT)) for p in (ROOT/"Solidity/Roadmap").rglob("*.lean")}
        self.assertEqual(set(c["unassigned_directory_files"]),observed-assigned)
        self.assertTrue(all("/G49Final/" not in p for p in assigned))
        self.assertEqual(len(assigned),15)

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
