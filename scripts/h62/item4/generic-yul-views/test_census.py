#!/usr/bin/env python3
"""Adversarial inventory acceptance controls; external tests, not Lean proofs."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("census", Path(__file__).with_name("census.py"))
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

class InventoryControls(unittest.TestCase):
    def scan_text(self, text):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            views = root / "Solidity/Yul/Views"
            views.mkdir(parents=True)
            (views / "Controls.lean").write_text(text)
            return census.scan(root)

    def test_comment_and_string_decoys(self):
        data = self.scan_text('/- theorem fake : False := by sorry /- nested -/ -/\n'
            'def text := "theorem fake : False := by sorry"\n'
            'theorem real (h : True := True.intro) : True := h\n')
        self.assertEqual([d["name"] for d in data["declarations"]], ["text", "real"])
        self.assertIn('(h : True := True.intro) : True', data["declarations"][1]["statement"])
        self.assertNotIn(':= h', data["declarations"][1]["statement"])

    def test_guard_expectation_ownership(self):
        data = self.scan_text('/-- info: first -/\n#guard_msgs in\n#eval 1\n'
            '/-- info: second -/\n#guard_msgs in\n#eval 2\n')
        guards = data["declarations"]
        self.assertEqual([d["expected_message_comment"] for d in guards],
            ['/-- info: first -/', '/-- info: second -/'])
        self.assertNotIn('second', guards[0]["statement"])
        self.assertIn('#eval 1', guards[0]["statement"])
        self.assertNotIn('#eval 2', guards[0]["statement"])

    def test_attribute_and_where_identifier(self):
        data = self.scan_text('def previous := 0\n@[irreducible]\n'
            'def value := 1\ntheorem foo_where : True := True.intro\n'
            'theorem «where» : True := True.intro\n')
        ds = data["declarations"]
        self.assertNotIn('@[irreducible]', ds[0]["statement"])
        self.assertTrue(ds[1]["statement"].startswith('@[irreducible]'))
        self.assertEqual(ds[2]["statement"], 'theorem foo_where : True ')
        self.assertEqual(ds[3]["statement"], 'theorem «where» : True ')
        quoted = self.scan_text('theorem «has where inside» : True := True.intro\n')
        self.assertEqual(quoted["declarations"][0]["statement"], 'theorem «has where inside» : True ')

    def test_local_and_scoped_instances(self):
        data = self.scan_text('local instance localDecision : Decidable True := isTrue True.intro\n'
            'scoped instance scopedDecision : Decidable True := isTrue True.intro\n')
        self.assertEqual([d["name"] for d in data["declarations"]], ['localDecision', 'scopedDecision'])

    def test_missing_root_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError): census.scan(Path(tmp))

    def test_malformed_comment_refused(self):
        with self.assertRaises(ValueError): self.scan_text('/- unfinished')

    def test_type_mutation_changes_statement_hash(self):
        before = self.scan_text('theorem caseA : True := True.intro\n')
        after = self.scan_text('theorem caseA : False := False.elim h\n')
        self.assertNotEqual(before["declarations"][0]["statement_sha256"],
            after["declarations"][0]["statement_sha256"])

if __name__ == "__main__": unittest.main()
