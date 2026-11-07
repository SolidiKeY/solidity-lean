import importlib.util
import unittest
from pathlib import Path
spec=importlib.util.spec_from_file_location("census",Path(__file__).with_name("census.py"))
census=importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

class CensusTest(unittest.TestCase):
    def test_nested_comment_string_and_binder(self):
        source='''namespace N
/- outer /- theorem fake : False := by -/ end -/
private def fixture : String := "theorem fake := -- /-"
theorem kept (x : Nat := 3) : x = x := by rfl
end N
'''
        rows=census.declarations(source,"Controls.lean")
        self.assertEqual([r["name"] for r in rows],["N.fixture","N.kept"])
        self.assertEqual(rows[1]["statement"],"theorem kept (x : Nat := 3) : x = x")
        self.assertTrue(rows[1]["candidate_case"])
    def test_namespace_section(self):
        rows=census.declarations("namespace A\nsection\ntheorem x : True := trivial\nend\nnamespace B\ntheorem y : True := trivial\nend B\nend A\n", "X.lean")
        self.assertEqual([r["name"] for r in rows],["A.x","A.B.y"])
    def test_mutual_does_not_close_namespace(self):
        rows=census.declarations("namespace A\nmutual\ndef x : Nat := 0\ndef y : Nat := x\nend\ntheorem t : x = y := rfl\nend A\n", "X.lean")
        self.assertEqual([r["name"] for r in rows],["A.x","A.y","A.t"])
    def test_ambient_binder_drift_and_scope(self):
        source="namespace A\nsection\nvariable {n : Nat}\ntheorem t : n = n := rfl\nend\ntheorem u : True := trivial\nend A\n"
        a=census.declarations(source,"X.lean")
        b=census.declarations(source.replace("n : Nat","n : Int"),"X.lean")
        self.assertEqual(a[0]["header_sha256"],b[0]["header_sha256"])
        self.assertNotEqual(a[0]["statement_sha256"],b[0]["statement_sha256"])
        self.assertEqual(a[1]["ambient_binders"],[])
    def test_statement_and_proof_drift(self):
        a=census.declarations("theorem t : True := by trivial\n", "Controls.lean")[0]
        b=census.declarations("theorem t : True := True.intro\n", "Controls.lean")[0]
        c=census.declarations("theorem t : False := by trivial\n", "Controls.lean")[0]
        self.assertEqual(a["statement_sha256"],b["statement_sha256"])
        self.assertNotEqual(a["declaration_sha256"],b["declaration_sha256"])
        self.assertNotEqual(a["statement_sha256"],c["statement_sha256"])
    def test_proposition_let_assignments_are_part_of_statement(self):
        source="theorem t : let x := 1; let y := x + 1; y = 2 := by rfl\n"
        row=census.declarations(source,"Controls.lean")[0]
        self.assertEqual(row["statement"],source.split(" := by")[0])
        self.assertNotEqual(row["statement_sha256"],row["legacy_v1_statement_sha256"])
    def test_where_substring_is_not_keyword(self):
        row=census.declarations("theorem somewhere : True := trivial\n","Controls.lean")[0]
        self.assertEqual(row["statement"],"theorem somewhere : True")
    def test_unterminated_refuses(self):
        with self.assertRaises(ValueError): census.mask("/- unfinished")
        with self.assertRaises(ValueError): census.mask('"unfinished')

if __name__=="__main__": unittest.main()
