import json
import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import raw_tokens as t

class RawTokenTests(unittest.TestCase):
    def test_full_inventory(self):
        data = t.inventory(ROOT)
        self.assertEqual(len(data), 102)
        self.assertEqual(sum(map(len, data.values())), 1933)
        self.assertEqual(t.summary(data), json.loads(t.MANIFEST.read_text()))
    def test_comments_strings_nested_and_inline(self):
        source = "case x => | z\n-- case |\n/- | /- case -/ | -/\n\"case | \\\" escaped\"\ncasey case\x27 case |"
        self.assertEqual(t.tokens(source), [
            {"kind":"case", "line":1, "column":1}, {"kind":"pipe", "line":1, "column":11},
            {"kind":"case", "line":5, "column":13}, {"kind":"pipe", "line":5, "column":18}])
    def test_schema_and_mutations(self):
        for source in ["/- unclosed", "\"unclosed"]:
            with self.assertRaises(ValueError): t.tokens(source)
        original = t.tokens("case a => | b\n| c")
        self.assertNotEqual(original, t.tokens("case a => b\n| c"))
        self.assertNotEqual(original, t.tokens("case a => | b\n| c\n| d"))
        self.assertNotEqual(original, t.tokens("| c\ncase a => | b"))

if __name__ == "__main__": unittest.main()
