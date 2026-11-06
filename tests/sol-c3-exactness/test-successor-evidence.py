"""Targeted checks for portable timing and immutable successor evidence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

gate = load('c3_gate', 'scripts/check-sol-c3-exactness.py')
runner = load('c3_runner', 'tests/sol-c3-exactness/run-bounded.py')


class SuccessorEvidence(unittest.TestCase):
    def test_timing_preserves_actual_failure(self):
        result = subprocess.run([sys.executable, '-c', runner.TIMING_CODE,
                                 sys.executable, '-c', 'raise SystemExit(7)'],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 7)
        self.assertIn('Exit status: 7', result.stdout)
        self.assertIn('Maximum child resident set size', result.stdout)

    def test_signal_is_reported_as_posix_status(self):
        result = subprocess.run([sys.executable, '-c', runner.TIMING_CODE,
                                 sys.executable, '-c', 'import os,signal; os.kill(os.getpid(),signal.SIGTERM)'],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 143)
        self.assertIn('Raw child return code: -15', result.stdout)
        self.assertIn('Exit status: 143', result.stdout)

    def test_cached_build_cannot_hide_failed_direct_audit(self):
        # Synthetic unit receipts only: this is not kernel execution evidence.
        model = json.loads((gate.AREA / 'manifest.json').read_text())
        snapshot = {p: gate.sha((ROOT / p).read_bytes()) for p in
                    gate.REQUIRED | gate.TOOLING | set(model['modules'])}
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            build_log = folder / 'build.log'
            build_log.write_text('Build completed successfully\nExit status: 0\n')
            direct_log = folder / 'direct.log'
            direct_log.write_text('error: missing import object\nExit status: 1\n')
            common = {'input_hashes': snapshot, 'memory_limit_bytes': 12884901888,
                      'swap_limit_bytes': 0, 'minimum_parent_available_bytes': 4 * 1024**3,
                      'lean_version': 'Lean (version 4.24.0, test)',
                      'lake_version': 'Lake version 5.0.0-src+797c613',
                      'pressure_stop': False, 'interrupted': False}
            build = dict(common, command=['lake', 'build', '+Solidity.Frontend.C3Exactness.Audit'],
                         exit=0, log_sha256=gate.sha(build_log.read_bytes()))
            direct = dict(common, command=['lake', 'lean', 'Solidity/Frontend/C3Exactness/Audit.lean',
                                          '--', '-j1', '--tstack=131072'],
                          exit=1, log_sha256=gate.sha(direct_log.read_bytes()))
            build_receipt = folder / 'build.json'
            direct_receipt = folder / 'direct.json'
            build_receipt.write_text(json.dumps(build))
            direct_receipt.write_text(json.dumps(direct))
            paths = {'audit_log': build_log, 'audit_receipt': build_receipt,
                     'direct_log': direct_log, 'direct_receipt': direct_receipt}
            with patch.object(gate, 'bound_evidence', side_effect=lambda key, legacy: paths[key]):
                errors = gate.validate(model)
            self.assertIn('direct kernel audit has not passed', errors)

    def test_verified_evidence_cannot_change(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / 'tests/sol-c3-exactness'
            area.mkdir(parents=True)
            log = area / 'audit.log'
            log.write_bytes(b'original checked output')
            record = {'path': str(log.relative_to(root)),
                      'sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
            (area / 'SUCCESSOR-EVIDENCE.json').write_text(json.dumps({'audit_log': record}))
            with patch.object(gate, 'ROOT', root), patch.object(gate, 'AREA', area):
                self.assertEqual(gate.bound_evidence('audit_log', area / 'legacy'), log)
                log.write_bytes(b'changed')
                with self.assertRaisesRegex(ValueError, 'digest drift'):
                    gate.bound_evidence('audit_log', area / 'legacy')

    def test_evidence_cannot_escape_owned_area(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / 'tests/sol-c3-exactness'
            area.mkdir(parents=True)
            (area / 'SUCCESSOR-EVIDENCE.json').write_text(json.dumps(
                {'audit_log': {'path': '../outside', 'sha256': '0' * 64}}))
            with patch.object(gate, 'ROOT', root), patch.object(gate, 'AREA', area):
                with self.assertRaisesRegex(ValueError, 'escapes'):
                    gate.bound_evidence('audit_log', area / 'legacy')


if __name__ == '__main__':
    unittest.main()
