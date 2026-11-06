import unittest
from correspondence import compare

class CorrespondenceControls(unittest.TestCase):
    original = "theorem byte_component : True := True.intro\ntheorem byte_component_decode : True := True.intro\n"
    candidate = "theorem original_byte_component : True := True.intro\ntheorem original_byte_component_decode : True := True.intro\n"
    def test_exact_instances(self):
        self.assertEqual(len(compare(self.original,self.candidate)),2)
    def test_changed_observation_refused(self):
        with self.assertRaises(ValueError): compare(self.original,self.candidate.replace(': True', ': False',1))
    def test_changed_string_literal_refused(self):
        original = self.original.replace('True', '"before" = "before"')
        candidate = self.candidate.replace('True', '"after!" = "after!"')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_changed_literal_whitespace_refused(self):
        original = self.original.replace(': True', ': "a b" = "a b"')
        candidate = self.candidate.replace(': True', ': "a  b" = "a  b"')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_literal_syntax_is_not_a_boundary(self):
        original = self.original.replace(': True', ': "x := where" = "x := where"')
        candidate = self.candidate.replace(': True', ': "x := where" = "x := where"')
        self.assertEqual(len(compare(original, candidate)), 2)
    def test_escaped_literal_whitespace_refused(self):
        original = self.original.replace(': True', r': "a\n  b" = "a\n  b"')
        candidate = self.candidate.replace(': True', r': "a\n b" = "a\n b"')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_raw_literal_refused(self):
        original = self.original.replace(': True', ': r#"a" b c"# = r#"a" b c"#')
        candidate = self.candidate.replace(': True', ': r#"a" b  c"# = r#"a" b c"#')
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_character_literal_refused(self):
        original = self.original.replace(': True', ": (' ' : Char) = ' '")
        candidate = self.candidate.replace(': True', ": ('\t' : Char) = ' '")
        with self.assertRaises(ValueError): compare(original, candidate)
    def test_dropped_instance_refused(self):
        with self.assertRaises(ValueError): compare(self.original,self.candidate.splitlines()[0])

if __name__ == "__main__": unittest.main()
