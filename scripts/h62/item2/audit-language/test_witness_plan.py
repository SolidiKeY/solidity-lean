"""Guard false source credit from duplicates, guarded mismatches and malformed associations."""
import unittest
from witness_plan import associations, unique, code


class WitnessPlanTests(unittest.TestCase):
    def test_guarded_negative_separate(self):
        source = "namespace N\ntheorem w : True := True.intro\n#verify_hypotheses w for Solidity.T\n#guard_msgs in\n#verify_hypotheses w for Solidity.Bad\nend N\n"
        rows, negatives = associations("fixture", source)
        self.assertEqual(rows, [{"module": "fixture", "witness": "N.w", "target": "Solidity.T"}])
        self.assertEqual(len(negatives), 1)

    def test_duplicate_targets_and_witnesses(self):
        for second in ({"witness": "N.v", "target": "Solidity.T"},
                       {"witness": "N.w", "target": "Solidity.U"}):
            with self.subTest(second=second), self.assertRaises(ValueError):
                unique([{"witness": "N.w", "target": "Solidity.T"}, second])

    def test_unresolved_and_guard_syntax_refused(self):
        for source in ("#verify_hypotheses absent for Solidity.T\n",
                       "#guard_msgs in\n", "#guard_msgs in\nexample : True := True.intro\n",
                       "#verify_hypotheses broken\n",
                       "#guard_msgs (whitespace := lax) in\n#verify_hypotheses absent for Solidity.T\n",
                       "#guard_msgs in #verify_hypotheses absent for Solidity.T\n"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                associations("fixture", source)

    def test_ambiguous_short_witness_refused(self):
        source = "namespace A\ntheorem w : True := True.intro\nend A\nnamespace B\ntheorem w : True := True.intro\nend B\n#verify_hypotheses w for Solidity.T\n"
        with self.assertRaises(ValueError):
            associations("fixture", source)

    def test_generated_code_has_real_newlines_and_quoted_module(self):
        report = {"rows": [{"module": "tests/h62/item2/audit-language/Fixture.lean",
                            "witness": "N.w", "target": "Solidity.T"}]}
        generated = code(report)
        self.assertIn(".«audit-language».", generated)
        self.assertIn("\n#audit_witness N.w for Solidity.T\n", generated)
        self.assertNotIn("\\n", generated)

    def test_comments_do_not_create_credit(self):
        rows, negatives = associations("fixture", "/- #verify_hypotheses fake for Solidity.T -/\n")
        self.assertEqual((rows, negatives), ([], []))


if __name__ == "__main__":
    unittest.main()
