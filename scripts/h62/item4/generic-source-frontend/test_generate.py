#!/usr/bin/env python3
"""Refuse a missing/reordered/weakened original fixture universe."""
import shutil
import tempfile
import unittest
from pathlib import Path
from generate import generated, REPO, ORIGINAL, TARGET

class GenerationTests(unittest.TestCase):
    def test_exact_reproduction(self):
        for path, content in generated(REPO).items():
            self.assertEqual((REPO/path).read_text(), content)
    def test_missing_original_is_refused(self):
        with tempfile.TemporaryDirectory() as root:
            target = Path(root)/ORIGINAL
            shutil.copytree(REPO/ORIGINAL, target)
            (target/'Case44.lean').unlink()
            with self.assertRaises(ValueError):
                generated(Path(root))
    def test_weakened_statement_is_refused(self):
        with tempfile.TemporaryDirectory() as root:
            target = Path(root)/ORIGINAL
            shutil.copytree(REPO/ORIGINAL, target)
            path = target/'Case00.lean'
            path.write_text(path.read_text().replace('statementFixtureCheck statementFixture0 = true', 'True'))
            with self.assertRaises(ValueError):
                generated(Path(root))
    def test_one_certificate_per_declaration(self):
        table = generated(REPO)[TARGET/'FixtureTable.lean']
        self.assertEqual(table.count('by decide +kernel'), 45)
        self.assertEqual(table.count('private theorem certificate'), 45)
        self.assertEqual(table.count('theorem instance'), 45)

if __name__ == '__main__':
    unittest.main()
