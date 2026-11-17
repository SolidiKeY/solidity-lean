#!/usr/bin/env python3
"""Regression controls for a fresh checkout without an empty registry directory."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("p16_generator", Path(__file__).with_name("generate.py"))
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)

class EmptyRegistryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.module = "Solidity.Yul.EmptyRegistryControl"
        self.body = "/-! Baseline control. -/\n"
        inventory = {}
        for kind, data in {"imports": (self.module + "\n").encode(), "body": self.body.encode()}.items():
            (self.root / kind).mkdir()
            (self.root / kind / "001.txt").write_bytes(data)
            inventory[kind] = {"001.txt": hashlib.sha256(data).hexdigest()}
        (self.root / "baseline-inventory.json").write_text(json.dumps(inventory))
        current = patch.object(generator, "HERE", self.root)
        current.start()
        self.addCleanup(current.stop)

    def test_absent_registry_preserves_baseline(self):
        self.assertFalse((self.root / "registrations").exists())
        nodes, text = generator.render(require_sources=False)
        self.assertEqual(nodes, [self.module])
        self.assertEqual(text, "import " + self.module + "\n\n" + self.body)

    def test_unregistered_import_still_refused(self):
        (self.root / "imports/ext-VY1-Lost.txt").write_text("Solidity.Yul.Lost\n")
        with self.assertRaisesRegex(ValueError, "imports fragment mismatch"):
            generator.registered_fragments()

    def test_unregistered_documentation_still_refused(self):
        (self.root / "body/ext-VY1-Lost.txt").write_text("/-! Lost. -/\n")
        with self.assertRaisesRegex(ValueError, "body fragment mismatch"):
            generator.registered_fragments()

    def test_dangling_symlink_is_not_empty_registry(self):
        (self.root / "registrations").symlink_to(self.root / "missing", target_is_directory=True)
        with self.assertRaises(FileNotFoundError):
            generator.registered_fragments()

    def test_regular_file_is_not_empty_registry(self):
        (self.root / "registrations").write_text("not a directory")
        with self.assertRaises(NotADirectoryError):
            generator.registered_fragments()

    def test_missing_baseline_still_refused(self):
        (self.root / "imports/001.txt").unlink()
        with self.assertRaisesRegex(ValueError, "missing or changed baseline imports fragment"):
            generator.registered_fragments()

if __name__ == "__main__":
    unittest.main()
