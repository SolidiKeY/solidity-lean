"""Check original gate bytes and that successor metadata cannot select evidence."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
ORIGINAL = '21043c5220a7c0390810ec7088c83a6bd9c8ff8c'

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

gate = load('c3_gate', 'scripts/check-sol-c3-exactness.py')
runner = load('c3_runner', 'tests/sol-c3-exactness/run-bounded.py')


class TrackedEvidenceOnly(unittest.TestCase):
    def test_gate_is_byte_identical_to_original(self):
        path = 'scripts/check-sol-c3-exactness.py'
        expected = subprocess.check_output(['git', 'show', ORIGINAL + ':' + path], cwd=ROOT)
        self.assertEqual((ROOT / path).read_bytes(), expected)
        self.assertFalse(hasattr(gate, 'bound_evidence'))

    def test_self_declared_successor_index_is_never_read(self):
        model = json.loads((gate.AREA / 'manifest.json').read_text())
        expected = (gate.validate(model), gate.fixture_errors())
        index = gate.AREA / 'SUCCESSOR-EVIDENCE.json'
        original_read = Path.read_text
        observed = []
        def read_text(path, *args, **kwargs):
            if path == index:
                observed.append(path)
                # Even a malformed or self-consistent forged index is irrelevant.
                return '{"audit_log":{"path":"forged","sha256":"self-declared"}}'
            return original_read(path, *args, **kwargs)
        with patch.object(Path, 'read_text', read_text):
            actual = (gate.validate(model), gate.fixture_errors())
        self.assertEqual(observed, [])
        self.assertEqual(actual, expected)

    def test_timing_preserves_actual_failure(self):
        result = subprocess.run([sys.executable, '-c', runner.TIMING_CODE,
                                 sys.executable, '-c', 'raise SystemExit(7)'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 7)
        self.assertIn('Exit status: 7', result.stdout)

    def test_signal_is_reported_as_posix_status(self):
        result = subprocess.run([sys.executable, '-c', runner.TIMING_CODE,
                                 sys.executable, '-c', 'import os,signal; os.kill(os.getpid(),signal.SIGTERM)'],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 143)
        self.assertIn('Raw child return code: -15', result.stdout)


if __name__ == '__main__':
    unittest.main()
