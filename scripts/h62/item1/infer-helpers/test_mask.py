#!/usr/bin/env python3
"""Controls for the deliberately limited Lean text mask."""
import unittest
from lean_mask import mask

class MaskTest(unittest.TestCase):
    def test_nested_comments_strings_and_lines(self):
        text = "def live := 1\n/- outer /- inner -/ hidden -/\ndef next := \"escaped \\\" -- /-\" -- hidden\n"
        out = mask(text)
        self.assertEqual(len(out), len(text))
        self.assertEqual([i for i,c in enumerate(out) if c == "\n"], [i for i,c in enumerate(text) if c == "\n"])
        self.assertIn("def live", out)
        self.assertIn("def next", out)
        self.assertNotIn("inner", out)
        self.assertNotIn("escaped", out)
        self.assertNotIn("hidden", out)

    def test_malformed_and_unsupported_are_rejected(self):
        for text in ("/- unfinished", "\"unfinished", "«odd-name»", "r#\"raw\"#", "s!\"interpolated\""):
            with self.subTest(text=text), self.assertRaises(ValueError):
                mask(text)

if __name__ == "__main__":
    unittest.main()
