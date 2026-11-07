#!/usr/bin/env python3
"""Regression controls for original-map preservation after additive integration."""
import pathlib,sys,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item2/audit-evm-compiler'))
from rescan_original_scope import validate_additive_map
class ScopeControls(unittest.TestCase):
    original='# Scope\n| `A.lean` | original |\n'
    added='| `B.lean` | unassigned addition |\n'
    def test_addition(self):
        self.assertEqual(validate_additive_map(self.original,self.original+self.added),[self.added.strip()])
    def test_duplicate_heading(self):
        with self.assertRaisesRegex(ValueError,'non-module'):validate_additive_map(self.original,self.original+'# Scope\n')
    def test_duplicate_original_module(self):
        with self.assertRaisesRegex(ValueError,'duplicate current'):validate_additive_map(self.original,self.original+'| `A.lean` | duplicate description |\n')
    def test_duplicate_new_module(self):
        with self.assertRaisesRegex(ValueError,'duplicate current'):validate_additive_map(self.original,self.original+self.added+self.added)
    def test_removed_original(self):
        with self.assertRaisesRegex(ValueError,'removed or modified'):validate_additive_map(self.original,'# Scope\n')
    def test_modified_original(self):
        with self.assertRaisesRegex(ValueError,'removed or modified'):validate_additive_map(self.original,self.original.replace('original','changed'))
if __name__=='__main__':unittest.main(verbosity=2)
