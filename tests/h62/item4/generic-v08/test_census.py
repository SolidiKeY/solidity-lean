"""Source integrity tests: deliberately mutate statements, proof bodies and cases."""
import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location('census',Path(__file__).resolve().parents[4]/'scripts/h62/item4/generic-v08/census.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)

class Census(unittest.TestCase):
    def test_nested_comments_strings(self):
        s='/- theorem hidden : False := /- nested -/ x -/\ndef x : String := "theorem fake : False :="\ntheorem keep : True := by trivial\n'
        self.assertEqual([r['name'] for r in c.declarations('X',s)],['x','keep'])
    def test_body_not_in_statement(self):
        a='theorem exact (n : Nat) : n = n := by rfl\n'
        b=a.replace('by rfl','by exact Eq.refl n')
        self.assertEqual(c.declarations('X',a)[0]['statement_sha256'],c.declarations('X',b)[0]['statement_sha256'])
        self.assertNotEqual(c.digest(a),c.digest(b))
    def test_statement_mutation(self):
        a='theorem exact (n : Nat) : n = n := by rfl\n'
        b=a.replace('n = n','n = 0')
        self.assertNotEqual(c.declarations('X',a)[0]['statement_sha256'],c.declarations('X',b)[0]['statement_sha256'])
    def test_binder_default(self):
        s='def f (n : Nat := 1) : Nat := n\n'
        self.assertEqual(c.declarations('X',s)[0]['header'],'def f (n : Nat := 1) : Nat ')
    def test_equations(self):
        s='def f : Bool → Nat | false => 0 | true => 1\ndef g : Nat → Nat\n | n => n\n'
        self.assertEqual([r['name'] for r in c.declarations('X',s)],['f','g'])
    def test_anonymous_preserved(self):
        self.assertEqual(len(c.declarations('X','example : True := by trivial\nexample : True := by trivial\n')),2)
    def test_match_statement(self):
        s='theorem t (b : Bool) : (match b with | true => 1 | false => 0) = 0 := by rfl\n'
        row=c.declarations('X',s)[0]
        self.assertTrue(row['header'].endswith('= 0 '))
        s='theorem t (b : Bool) : True = match b with | true => True | false => False := by rfl\n'
        self.assertIn('| false => False',c.declarations('X',s)[0]['header'])
    def test_let_statement(self):
        s='theorem t : let x := 1; x = 1 := by rfl\n'
        self.assertTrue(c.declarations('X',s)[0]['header'].endswith('x = 1 '))
    def test_named_instance(self):
        self.assertEqual(c.declarations('X','instance named : Decidable True := inferInstance\n')[0]['name'],'named')
        self.assertTrue(c.declarations('X','instance : Decidable True := inferInstance\n')[0]['name'].startswith('@instance:'))
    def test_recursive_inventory(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            nested=root/c.FAMILY/'Sub'
            nested.mkdir(parents=True)
            (nested/'Extra.lean').write_text('theorem added : True := by trivial\n')
            self.assertEqual(len(c.inventory(root)['files']),1)
    def test_malformed_refused(self):
        with self.assertRaises(ValueError): c.mask('/- unterminated')
        with self.assertRaises(ValueError): c.declarations('X','theorem x : True\n')

if __name__=='__main__': unittest.main()
