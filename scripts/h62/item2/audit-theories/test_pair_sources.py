import subprocess
import unittest
from census import ROOT
from measure_census_pair import census_sources

class PairSourceTests(unittest.TestCase):
    def test_current_candidate_is_exact_single_change_from_committed_baseline(self):
        original=subprocess.check_output(["git","show","304bda598101b57459d717022181352128c5d02b:tests/h62/item2/audit-theories/ElaboratedCensus.lean"],cwd=ROOT,text=True)
        before,after=census_sources(original)
        self.assertEqual(before.replace("(Json.arr rows).pretty ++","(Json.arr rows).compress ++"),after)
        self.assertEqual(after,(ROOT/"tests/h62/item2/audit-theories/ElaboratedCensus.lean").read_text())
        self.assertIn("ppExpr info.type",after)
        self.assertIn("(reprStr info.type)",after)

if __name__=="__main__":unittest.main()
