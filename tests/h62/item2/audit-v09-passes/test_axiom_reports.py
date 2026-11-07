"""Guarded-report regression: bare, detached and fake prints are not pins.
These source tests make no Lean axiom-safety or witness-coverage claim.
"""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-v09-passes"))
import axiom_reports


class AxiomReportAcceptance(unittest.TestCase):
    def test_direct_guard_and_exact_span(self):
        source = "/-- expected -/\n#guard_msgs in\n  #print axioms A.t\n"
        row, = axiom_reports.reports(source)
        self.assertTrue(row["direct_guard"])
        self.assertEqual(row["token"], "A.t")
        a, b = row["character_span"]
        self.assertEqual(source[a:b], "#print axioms A.t")
        self.assertIsNone(row["actual_axioms"])
        self.assertEqual(row["target_resolution"], "pending Lean")

    def test_guard_only_covers_one_command(self):
        rows = axiom_reports.reports("#guard_msgs in\n#print axioms first\n#print axioms second\n")
        self.assertEqual([r["direct_guard"] for r in rows], [True, False])

    def test_intervening_command_detaches_guard(self):
        row, = axiom_reports.reports("#guard_msgs in\n#check Nat\n#print axioms t\n")
        self.assertFalse(row["direct_guard"])

    def test_comments_and_strings_do_not_fabricate_commands(self):
        source = 'def s := "#guard_msgs in"\n/- outer /- nested -/\n#print axioms fake\n-/\n-- #print axioms fake2\n#print axioms real\n'
        row, = axiom_reports.reports(source)
        self.assertEqual(row["token"], "real")
        self.assertFalse(row["direct_guard"])

    def test_guard_options_and_comments(self):
        row, = axiom_reports.reports("#guard_msgs (whitespace := lax) in\n/- comment -/\n#print axioms t\n")
        self.assertTrue(row["direct_guard"])


if __name__ == "__main__":
    unittest.main()
