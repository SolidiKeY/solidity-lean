"""Primed source declarations remain part of the frozen interface census."""
import importlib.util
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[4]
SCRIPT=ROOT/'scripts/h62/item6/migrate-frontend'
sys.path.insert(0,str(SCRIPT))
import parser_overlay as p
class ParserNameControls(unittest.TestCase):
    def test_primed_names_are_not_collapsed(self):
        census={'declaration_candidates':[{'path':p.PARSER,'kind':'def','unqualified_candidate':n} for n in ('contractPart',"contractPart'")]}
        names=p.frozen_names(census)
        self.assertIn("Solidity.Frontend.Checked.contractPart'",names)
        self.assertIn('Solidity.Frontend.Checked.contractPart',names)
        self.assertEqual(len(names),len(set(names)))
    def test_duplicate_source_names_are_rejected(self):
        row={'path':p.PARSER,'kind':'def','unqualified_candidate':'contractPart'}
        with self.assertRaisesRegex(ValueError,'Duplicate'):p.frozen_names({'declaration_candidates':[row,row]})
if __name__=='__main__':unittest.main()
