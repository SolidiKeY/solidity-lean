#!/usr/bin/env python3
"""Refusal/accounting controls for frozen lexical candidates, not Lean proofs."""
import copy
import subprocess
import unittest
from unittest.mock import patch
import census
from reconcile_frozen import frozen_inventory, reconcile
from test_correspondence import GitViewsFixture


class FrozenReconciliationControls(GitViewsFixture, unittest.TestCase):
    def original_inventory(self):
        return frozen_inventory(self.root, base=self.base)[0]

    def rows(self):
        return reconcile(self.original_inventory(), census.scan(self.root))

    def test_unchanged_candidates_are_not_semantic_acceptance(self):
        rows = self.rows()
        self.assertEqual(len(rows), 2)
        self.assertTrue(all(row["status"] == "same_file_command_candidate" for row in rows))
        self.assertTrue(all("accepted" not in row for row in rows))

    def test_frozen_snapshot_ignores_changed_worktree(self):
        self.path.write_text(self.original.replace(": True", ": False"))
        inventory = self.original_inventory()
        self.assertTrue(all(": True" in row["statement"] for row in inventory["declarations"]))
        self.assertTrue(all(row["status"] == "unmatched" for row in self.rows()))

    def test_move_to_noncontrols_file_retains_frozen_cases(self):
        self.path.rename(self.views / "Ordinary.lean")
        current = census.scan(self.root)
        self.assertEqual(current["summary"]["controls_files"], 0)
        rows = reconcile(self.original_inventory(), current)
        self.assertEqual(len(rows), 2)
        self.assertTrue(all(row["status"] == "other_file_command_candidate" for row in rows))
        self.assertTrue(all(not row["candidates"][0]["in_controls_file"] for row in rows))

    def test_deleted_declaration_is_unmatched_not_dropped(self):
        self.path.write_text(self.original.splitlines(keepends=True)[1])
        rows = self.rows()
        self.assertEqual(len(rows), 2)
        self.assertEqual(sum(row["status"] == "unmatched" for row in rows), 1)

    def test_proof_change_is_only_statement_candidate(self):
        self.path.write_text(self.original.replace("True.intro", "by exact True.intro"))
        self.assertTrue(all(row["status"] == "same_file_statement_candidate" for row in self.rows()))

    def test_duplicate_current_text_stays_ambiguous(self):
        (self.views / "Other.lean").write_text(self.original)
        rows = self.rows()
        self.assertEqual(len(rows), 2)
        self.assertTrue(all(row["status"] == "ambiguous_command_candidates" for row in rows))
        self.assertTrue(all(len(row["candidates"]) == 2 for row in rows))

    def test_new_cases_do_not_expand_original_universe(self):
        (self.views / "AddedControls.lean").write_text("theorem added : True := True.intro\n")
        self.assertEqual(len(self.rows()), 2)
        self.assertNotIn("added", [row["original"]["name"] for row in self.rows()])

    def test_duplicate_frozen_position_refused(self):
        original = self.original_inventory()
        original["declarations"].append(copy.deepcopy(original["declarations"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate frozen"):
            reconcile(original, census.scan(self.root))

    def test_empty_frozen_control_universe_refused(self):
        with self.assertRaisesRegex(ValueError, "empty frozen"):
            reconcile({"declarations": []}, census.scan(self.root))

    def test_corrupt_frozen_object_refused_before_scanning(self):
        blob = self.git("rev-parse", self.base + ":Solidity/Yul/Views/ReadControls.lean").decode().strip()
        raw = self.original.encode()
        corrupt = (blob + " blob " + str(len(raw)) + "\n").encode() + b"X" + raw[1:] + b"\n"
        actual = subprocess.check_output
        def output(argv, **kwargs):
            return corrupt if argv[:2] == ["git", "cat-file"] else actual(argv, **kwargs)
        with patch("reconcile_frozen.subprocess.check_output", side_effect=output):
            with self.assertRaisesRegex(ValueError, "frozen object mismatch"):
                self.original_inventory()


if __name__ == "__main__": unittest.main()
