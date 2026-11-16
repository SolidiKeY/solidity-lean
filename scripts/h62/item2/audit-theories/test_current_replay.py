import tempfile,unittest
from pathlib import Path
from replay_current_helpers import helper_targets,require_complete_targets

class CurrentReplayTests(unittest.TestCase):
    def test_nested_helpers_discovered(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);base=root/"tests/h62/item2/audit-theories";(base/"nested").mkdir(parents=True)
            for name in ("A.lean","ElaboratedCensus.lean","nested/B.lean"):(base/name).write_text("")
            self.assertEqual(helper_targets(root),["tests/h62/item2/audit-theories/A.lean","tests/h62/item2/audit-theories/nested/B.lean"])
    def test_complete_unordered_census(self):
        require_complete_targets(["a","nested/b"],{"modules":[{"source":"nested/b"},{"source":"a"}]})
    def test_unreplayed_nested_certificate_refused(self):
        with self.assertRaisesRegex(AssertionError,"recursive replay targets"):
            require_complete_targets(["a"],{"modules":[{"source":"a"},{"source":"nested/b"}]})
    def test_duplicate_certificate_row_refused(self):
        with self.assertRaisesRegex(AssertionError,"recursive replay targets"):
            require_complete_targets(["a"],{"modules":[{"source":"a"},{"source":"a"}]})
if __name__=="__main__":unittest.main()
