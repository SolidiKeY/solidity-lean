"""Reject substituted scope/source bytes and unsafe recovery destinations."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('recover', HERE/'reproduce_frozen.py')
recover = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(recover)
REPO = HERE.parents[3]


class RecoveryGuards(unittest.TestCase):
    def test_existing_destination_unchanged(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp)
            marker = target/'marker'
            marker.write_bytes(b'preserve')
            with self.assertRaises(FileExistsError):
                recover.reproduce(REPO, target)
            self.assertEqual(marker.read_bytes(), b'preserve')
            self.assertEqual(list(target.iterdir()), [marker])

    def test_checkout_destination_refused(self):
        with self.assertRaises(ValueError):
            recover.reproduce(REPO, REPO/'recovery-test-must-not-exist')
        self.assertFalse((REPO/'recovery-test-must-not-exist').exists())

    def test_scope_substitution_refused_before_writes(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp)/'output'
            with patch.object(recover.subprocess, 'check_output', return_value=b'{}'):
                with self.assertRaisesRegex(ValueError, 'scope authentication'):
                    recover.reproduce(REPO, target)
            self.assertFalse(target.exists())

    def test_frozen_source_substitution_refused_before_writes(self):
        original = subprocess.check_output
        def tampered(command):
            if command[-1].startswith(recover.BASE+':'):
                return b'changed source'
            return original(command)
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp)/'output'
            with patch.object(recover.subprocess, 'check_output', side_effect=tampered):
                with self.assertRaisesRegex(ValueError, 'frozen source mismatch'):
                    recover.reproduce(REPO, target)
            self.assertFalse(target.exists())


if __name__ == '__main__':
    unittest.main()
