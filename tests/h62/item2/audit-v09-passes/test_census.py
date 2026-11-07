#!/usr/bin/env python3
"""Acceptance for census fidelity, including review-discovered regressions."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location("census", ROOT / "scripts/h62/item2/audit-v09-passes/census.py")
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)


class CensusAcceptance(unittest.TestCase):
    def test_comments_strings_and_nested_scope(self):
        source = r'''namespace A
/- outer /- nested -/
theorem fake : False := by contradiction
-/
def label := "theorem fake2 : False := by contradiction"
section s
namespace B
-- theorem fake3 : False := by contradiction
protected theorem real (x : Nat) : x = x := by rfl
end B
end s
end A
'''
        rows = census.declarations("fixture.lean", source)
        self.assertEqual([r["name"] for r in rows], ["A.B.real"])
        self.assertEqual(rows[0]["signature"], "protected theorem real (x : Nat) : x = x")
        self.assertEqual(rows[0]["visibility"], "protected")

    def test_top_level_lets_and_nested_assignments(self):
        statement = "theorem t (m : Nat) : ∀ tail, let cm := {m with x := tail}\n  let em := cm\n  em = cm"
        rows = census.declarations("fixture.lean", statement + " := by rfl\n")
        self.assertEqual(rows[0]["signature"], statement)

    def test_identifier_ending_in_let(self):
        statement = "theorem t : outlet = outlet"
        self.assertEqual(census.declarations("fixture.lean", statement + " := by rfl")[0]["signature"], statement)

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError):
            census.masked("/- unterminated")

    def test_frozen_review_regressions_and_census(self):
        result = census.census(ROOT)
        self.assertEqual(result["summary"], {"files": 179, "declarations": 1259,
                                            "witnesses_verified": 0, "uncovered": 1259})
        rows = result["declarations"]
        lets = [r for r in rows if "let " in r["signature"]]
        self.assertEqual(len(lets), 9)
        for row in rows:
            source = (ROOT / row["path"]).read_text()
            start, end = row["character_span"]
            self.assertEqual(source[start:end].strip(), row["signature"])
            self.assertEqual(source[end:end+2], ":=")
            self.assertEqual(row["witness_status"], "uncovered")
        for row in lets:
            source = (ROOT / row["path"]).read_text()
            end = row["character_span"][1]
            # Independent frozen-tree oracle: all nine end with the line's
            # final proof separator, never a let definition separator.
            self.assertRegex(source[end:end+100], r"^:=\s+(by|rfl|General\.source_execution)\b")
            self.assertGreaterEqual(row["signature"].count(":="), 1)
        self.assertEqual(sum(r["visibility"] == "private" for r in rows), 190)


if __name__ == "__main__":
    unittest.main()
