"""Negative controls for census false edges and nested comments."""
import importlib.util, pathlib, unittest
script=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-automation/census.py'
spec=importlib.util.spec_from_file_location('census',script); c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
class CensusTests(unittest.TestCase):
    def test_comments(self):
        self.assertEqual(c.imports('/- import False\n /- nested -/\n import Other -/\nimport Real\n-- import Nope'),['Real'])
    def test_string_comment_markers(self):
        self.assertEqual(c.imports('def x := "/- --"\nimport Real -- ignored'),['Real'])
    def test_many_imports(self):
        self.assertEqual(c.imports('import A B\npublic import C\nmeta import D'),['A','B','C','D'])
    def test_multiline_string(self):
        self.assertEqual(c.imports('def x := "\nimport False\n"\nimport Real'),['Real'])
    def test_unterminated(self):
        with self.assertRaises(ValueError):c.imports('/- unclosed')
if __name__=='__main__': unittest.main()
