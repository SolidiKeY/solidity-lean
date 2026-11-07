import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lexical_mask import mask_comments_and_strings

class LexicalMaskTest(unittest.TestCase):
    def test_raw_strings_with_hash_delimiters(self):
        source = 'r##"inside " and panicData then "# more"##\npanicData\n'
        masked = mask_comments_and_strings(source)
        self.assertEqual(len(masked), len(source))
        self.assertEqual([i for i, c in enumerate(masked) if c == "\n"],
                         [i for i, c in enumerate(source) if c == "\n"])
        self.assertNotIn("inside", masked)
        self.assertEqual(masked.count("panicData"), 1)
        self.assertEqual(mask_comments_and_strings('r"raw" panicData').count("panicData"), 1)
        with self.assertRaisesRegex(ValueError, "unterminated raw string"):
            mask_comments_and_strings('r#"unterminated"')

    def test_interpolation_fails_closed_outside_comments_and_strings(self):
        for source in ('s!"{panicData}"', 's!"{x "nested" y}"', 'm! "text {panicData}"', 'α!"{panicData}"', '«quoted name»!"{panicData}"', 's!/-comment-/"{panicData}"', 's!--comment\n"{panicData}"'):
            with self.assertRaisesRegex(ValueError, "possible interpolated string syntax is unsupported"):
                mask_comments_and_strings(source)
        source = '-- s!"{panicData}"\n"s! is text"\npanicData\n'
        self.assertEqual(mask_comments_and_strings(source).count("panicData"), 1)

if __name__ == "__main__": unittest.main()
