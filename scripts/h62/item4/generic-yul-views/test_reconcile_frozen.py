#!/usr/bin/env python3
"""Refusal/accounting controls for frozen lexical candidates, not Lean proofs."""
import copy
from pathlib import Path
from types import SimpleNamespace
import subprocess
import unittest
from unittest.mock import patch
import census
from reconcile_frozen import frozen_inventory, reconcile, namespace_hints, _namespace_parser
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

    def namespace_rows(self):
        original, _ = frozen_inventory(self.root, base=self.base)
        current = census.scan(self.root)
        rows = reconcile(original, current)
        hints = namespace_hints(self.root, original, current, rows, base=self.base)
        return rows, hints

    def namespace_fixture(self, other="Other", private=False):
        text = self.original.replace("theorem ", "private theorem ") if private else self.original
        self.path.write_text("namespace Original\n" + text + "end Original\n")
        self.freeze()
        (self.views / "Other.lean").write_text("namespace " + other + "\n" + text + "end " + other + "\n")

    def test_namespace_hint_keeps_original_ambiguity_and_candidates(self):
        self.namespace_fixture()
        rows, hints = self.namespace_rows()
        self.assertEqual(hints["summary"], {"unique_source_name_hint_candidate": 2})
        self.assertTrue(all(row["status"] == "ambiguous_command_candidates" for row in rows))
        self.assertTrue(all(len(row["candidates"]) == 2 for row in rows))
        self.assertTrue(all(len(row["namespace_hints"]["matching_candidates"]) == 1 for row in rows))
        self.assertTrue(all("accepted" not in row for row in rows))

    def test_private_source_names_do_not_identify_mangled_declarations(self):
        self.namespace_fixture(other="Original", private=True)
        rows, hints = self.namespace_rows()
        self.assertEqual(hints["summary"], {"ambiguous_source_name_hint_candidates": 2})
        self.assertTrue(all(len(row["namespace_hints"]["matching_candidates"]) == 2 for row in rows))
        self.assertTrue(all(row["namespace_hints"]["original_context"]["visibility"] == "private" for row in rows))

    def test_missing_namespace_context_does_not_drop_cases(self):
        self.namespace_fixture()
        parser = SimpleNamespace(declarations=lambda _: [])
        with patch("reconcile_frozen._namespace_parser", return_value=(parser, Path(__file__))):
            rows, hints = self.namespace_rows()
        self.assertEqual(hints["summary"], {"unavailable_context": 2})
        self.assertTrue(all(len(row["candidates"]) == 2 for row in rows))

    def test_one_unknown_candidate_prevents_unique_hint_status(self):
        self.namespace_fixture()
        actual, parser_path = _namespace_parser()
        def partial(path):
            return [] if path.endswith("Other.lean") else actual.declarations(path)
        with patch("reconcile_frozen._namespace_parser",
                return_value=(SimpleNamespace(declarations=partial), parser_path)):
            rows, hints = self.namespace_rows()
        self.assertEqual(hints["summary"], {"unavailable_context": 2})
        self.assertTrue(all(len(row["namespace_hints"]["matching_candidates"]) == 1 for row in rows))
        self.assertTrue(all(len(row["candidates"]) == 2 for row in rows))

    def test_changed_namespace_does_not_get_an_original_name_hint(self):
        self.namespace_fixture()
        self.path.write_text(self.path.read_text().replace("Original", "Changed"))
        rows, hints = self.namespace_rows()
        self.assertEqual(hints["summary"], {"no_matching_source_name_hint": 2})
        self.assertTrue(all(len(row["namespace_hints"]["matching_candidates"]) == 0 for row in rows))
        self.assertTrue(all(row["status"] == "ambiguous_command_candidates" for row in rows))

    def test_unsupported_namespace_context_is_explicit(self):
        self.namespace_fixture()
        def unsupported(path): raise ValueError("unsupported context " + path)
        parser = SimpleNamespace(declarations=unsupported)
        with patch("reconcile_frozen._namespace_parser", return_value=(parser, Path(__file__))):
            rows, hints = self.namespace_rows()
        self.assertEqual(hints["summary"], {"unavailable_context": 2})
        self.assertEqual(len(hints["extraction_errors"]), 3)
        self.assertTrue(all("views-namespace-" not in row["error"] for row in hints["extraction_errors"]))

    def test_stale_namespace_source_is_refused(self):
        self.namespace_fixture()
        original, _ = frozen_inventory(self.root, base=self.base)
        current = census.scan(self.root)
        rows = reconcile(original, current)
        self.path.write_text(self.path.read_text().replace("Original", "Changed"))
        with self.assertRaisesRegex(ValueError, "source changed before namespace"):
            namespace_hints(self.root, original, current, rows, base=self.base)


if __name__ == "__main__": unittest.main()
