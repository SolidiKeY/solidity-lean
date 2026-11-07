"""The mapFree text label must not hide a changed premise or extra argument."""
import unittest
from compare_source_drift import mapfree_text_pattern


class DriftPatterns(unittest.TestCase):
    def test_one_argument_with_formatting(self):
        self.assertTrue(mapfree_text_pattern('theorem t : f E.isBase x = true  ',
                                           'theorem t :\n f E.isBase E.mapFree x = true'))

    def test_whitespace_alone_is_not_argument_addition(self):
        self.assertFalse(mapfree_text_pattern('f x', 'f  x'))

    def test_changed_premise_is_not_hidden(self):
        self.assertFalse(mapfree_text_pattern('theorem t (h : False) : f E.isBase x = true',
                                            'theorem t : f E.isBase E.mapFree x = true'))

    def test_duplicate_argument_is_not_one_addition(self):
        self.assertFalse(mapfree_text_pattern('f E.isBase x',
                                            'f E.isBase E.mapFree E.mapFree x'))


if __name__=='__main__':
    unittest.main()
