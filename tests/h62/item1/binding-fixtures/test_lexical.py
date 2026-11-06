"""Focused lexical filter controls; no Lean parsing or proof claim."""
import pathlib,sys,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item1/binding-fixtures'))
from lexical import code_only, unknown_identifiers

class LexicalControls(unittest.TestCase):
    def test_nested_comments_offsets_and_lines(self):
        source='import Real\n/- outer\n/- nested -/\nimport Phantom\n-/\ndef actual := 1 -- hidden\n'
        masked=code_only(source)
        self.assertEqual(len(masked),len(source))
        self.assertEqual([i for i,c in enumerate(masked) if c=='\n'],[i for i,c in enumerate(source) if c=='\n'])
        self.assertIn('import Real',masked);self.assertIn('def actual',masked)
        self.assertNotIn('Phantom',masked);self.assertNotIn('hidden',masked)
    def test_strings_and_raw_strings(self):
        source='def text := "import False /- \\" still string"\ndef raw := r##"-- /- \" text"##\ndef actual := 1\n'
        masked=code_only(source)
        self.assertNotIn('False',masked);self.assertNotIn('still string',masked)
        self.assertIn('def actual',masked)
    def test_incomplete_input_fails_closed(self):
        for source in ['/- unclosed','"unclosed','r##"unclosed','«unclosed',chr(34)+'tail'+chr(92)]:
            with self.subTest(source=source),self.assertRaises(ValueError):code_only(source)
    def test_zero_hash_raw_backslash_and_quoted_identifier(self):
        source='def raw := r"-- /- '+chr(92)+'"\n'+'def «/- not comment --» := 1\ndef actual := 2\n'
        masked=code_only(source)
        self.assertIn('def actual := 2',masked)
        self.assertNotIn('not comment',masked)
        self.assertEqual(len(masked),len(source))

    def test_quoted_bindingrel_is_reported_unknown(self):
        source='def «BindingRel» := 1\n#check «BindingRel»\n'
        self.assertEqual(unknown_identifiers(source),[
            {'line':1,'text':'«BindingRel»','status':'unknown quoted identifier'},
            {'line':2,'text':'«BindingRel»','status':'unknown quoted identifier'}])
        self.assertNotIn('BindingRel',code_only(source))

    def test_identifier_apostrophe(self):
        self.assertEqual(code_only("def value' := 1\n"),"def value' := 1\n")

if __name__=='__main__':unittest.main(verbosity=2)
