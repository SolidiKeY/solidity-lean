"""Original gate preservation, optional artifact fallback, and portable timing."""
import ast
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
ORIGINAL = '21043c5220a7c0390810ec7088c83a6bd9c8ff8c'

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

gate = load('c3_gate', 'scripts/check-sol-c3-exactness.py')
runner = load('c3_runner', 'tests/sol-c3-exactness/run-bounded.py')


class SuccessorEvidence(unittest.TestCase):
    def test_original_gate_and_pin_are_preserved(self):
        path = 'scripts/check-sol-c3-exactness.py'
        original = subprocess.check_output(['git', 'show', ORIGINAL + ':' + path], cwd=ROOT, text=True)
        current = (ROOT / path).read_text()
        # Normalize only the coordinator-authorized evidence location adapter.
        current = current.replace(
            '    log_path = bound_evidence("audit_log", AREA / "evidence/audit-confirmation.log")\n'
            '    receipt_path = bound_evidence("audit_receipt", AREA / "evidence/audit-confirmation.log.json")',
            '    log_path = AREA / "evidence/audit-confirmation.log"\n'
            '    receipt_path = log_path.with_suffix(".log.json")')
        current = current.replace(
            '    log_path = str(bound_evidence("fixture_log", AREA / "evidence/compiler-fixtures-final.log").relative_to(ROOT))\n'
            '    fixture_receipt = str(bound_evidence("fixture_receipt", AREA / "evidence/compiler-fixtures-final.log.json").relative_to(ROOT))\n'
            '    receipt = receipt_override if receipt_override is not None else json.loads(read(fixture_receipt))',
            '    log_path = "tests/sol-c3-exactness/evidence/compiler-fixtures-final.log"\n'
            '    receipt = receipt_override if receipt_override is not None else json.loads(read(log_path + ".json"))')
        before = ast.parse(original)
        after = ast.parse(current)
        after.body = [node for node in after.body if not isinstance(node, ast.FunctionDef) or node.name != 'bound_evidence']
        self.assertEqual(ast.dump(before), ast.dump(after))

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

    def test_clean_checkout_falls_back_to_tracked_pairs(self):
        records = json.loads((gate.AREA / 'SUCCESSOR-EVIDENCE.json').read_text())
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / 'tests/sol-c3-exactness'
            area.mkdir(parents=True)
            (area / 'SUCCESSOR-EVIDENCE.json').write_text(json.dumps(records))
            with patch.object(gate, 'ROOT', root), patch.object(gate, 'AREA', area):
                for key in records:
                    legacy = area / ('tracked-' + key)
                    legacy.write_text('tracked evidence')
                    self.assertEqual(gate.bound_evidence(key, legacy), legacy)
                    self.assertEqual(legacy.read_text(), 'tracked evidence')

    def test_complete_pair_is_bound_and_partial_pair_falls_back(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / 'tests/sol-c3-exactness'
            area.mkdir(parents=True)
            log, receipt = area / 'audit.log', area / 'audit.json'
            log.write_bytes(b'checked output')
            receipt.write_bytes(b'receipt')
            records = {key: {'path': str(path.relative_to(root)),
                             'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                       for key, path in [('audit_log', log), ('audit_receipt', receipt)]}
            (area / 'SUCCESSOR-EVIDENCE.json').write_text(json.dumps(records))
            with patch.object(gate, 'ROOT', root), patch.object(gate, 'AREA', area):
                self.assertEqual(gate.bound_evidence('audit_log', area / 'legacy'), log)
                log.write_bytes(b'changed')
                with self.assertRaisesRegex(ValueError, 'digest drift'):
                    gate.bound_evidence('audit_log', area / 'legacy')
                receipt.unlink()
                self.assertEqual(gate.bound_evidence('audit_log', area / 'legacy'), area / 'legacy')
                self.assertEqual(gate.bound_evidence('audit_receipt', area / 'legacy-json'), area / 'legacy-json')

    def test_evidence_cannot_escape_owned_area(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / 'tests/sol-c3-exactness'
            area.mkdir(parents=True)
            record = {'path': '../outside', 'sha256': '0' * 64}
            (area / 'SUCCESSOR-EVIDENCE.json').write_text(json.dumps(
                {'audit_log': record, 'audit_receipt': record}))
            with patch.object(gate, 'ROOT', root), patch.object(gate, 'AREA', area):
                with self.assertRaisesRegex(ValueError, 'escapes'):
                    gate.bound_evidence('audit_log', area / 'legacy')


if __name__ == '__main__':
    unittest.main()
