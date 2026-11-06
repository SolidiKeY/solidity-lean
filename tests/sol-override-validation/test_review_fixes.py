"""Regression checks for failure propagation, immutable pins and bulk retrieval.
No Lean process or full gate is launched by these tests.
"""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import shlex
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import check_controls
import final_gates
from gate_runtime import Runner

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('override_gate', ROOT / 'scripts/check-sol-override-validation.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class ReviewFixes(unittest.TestCase):
    def runner_args(self, folder, fail):
        fake = folder / 'runner.py'
        fake.write_text('import sys\nraise SystemExit(7 if ' + repr(fail) + ' in " ".join(sys.argv[1:]) else 0)\n')
        return argparse.Namespace(runner=shlex.join([sys.executable, str(fake)]), local=False, output=folder / 'out')

    def test_failed_gate_survives_later_success(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.runner_args(Path(directory), 'check-solkey.sh')
            with patch.object(final_gates, 'arguments', return_value=args):
                self.assertEqual(final_gates.main(), 1)
            results = (args.output / 'final-gates.json').read_text()
            self.assertIn('"exitCode": 7', results)
            self.assertIn('"name": "final-resources"', results)

    def test_fresh_compiler_cannot_bypass_frozen_inputs(self):
        with patch.object(sys, 'argv', ['gate', '--compiler', '/not-read']), \
             patch.object(gate, 'verify_bulk_archive', return_value=Path('/verified')), \
             patch.object(gate, 'verify_recorded_bulk', side_effect=ValueError('frozen input differs')) as verify:
            with self.assertRaisesRegex(ValueError, 'frozen input differs'):
                gate.main()
            verify.assert_called_once_with(Path('/verified'), None, False)

    def test_live_process_prevents_first_diagnostic(self):
        with tempfile.TemporaryDirectory() as directory:
            # Fail the process-list probe; no diagnostic may then execute.
            args = self.runner_args(Path(directory), 'ps -eo')
            with patch.object(final_gates, 'arguments', return_value=args):
                self.assertEqual(final_gates.main(), 1)
            results = (args.output / 'final-gates.json').read_text()
            self.assertNotIn('final-diag-', results)

    def test_success_and_missing_executable(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.runner_args(Path(directory), 'never-matches')
            runner = Runner(args, 'test')
            self.assertEqual(runner.run('ok', ['true']), 0)
            self.assertEqual(runner.status(), 0)
            runner.prefix = ['/missing/override-runner']
            self.assertEqual(runner.run('missing', ['true']), 127)
            self.assertEqual(runner.status(), 1)

    def test_controls_compare_without_writing_on_success_or_failure(self):
        paths = [ROOT / f'tests/sol-override-validation/{name}.lean' for name in check_controls.CONTROLS]
        before = {p: p.read_bytes() for p in paths}
        for fail, expected in [('GraphControls.lean', 1), ('never-matches', 0)]:
            with tempfile.TemporaryDirectory() as directory:
                args = self.runner_args(Path(directory), fail)
                with patch.object(check_controls, 'arguments', return_value=args):
                    self.assertEqual(check_controls.main(), expected)
        self.assertEqual(before, {p: p.read_bytes() for p in paths})

    def test_pin_comparison_failure_is_not_rewritten(self):
        # A failed Lean command (including a #guard_msgs mismatch) must propagate.
        with tempfile.TemporaryDirectory() as directory:
            args = self.runner_args(Path(directory), 'Trust.lean')
            with patch.object(check_controls, 'arguments', return_value=args):
                self.assertEqual(check_controls.main(), 1)

    def test_bulk_restore_in_clean_checkout_and_reject_corruption(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tests = root / 'tests/sol-override-validation'
            tests.mkdir(parents=True)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            source = root / 'input.json'
            source.write_text('{"test":true}\n')
            archive = root / 'bulk.tar.gz'
            with tarfile.open(archive, 'w:gz') as output:
                output.add(source, arcname='tests/sol-override-validation/matrix.json')
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            (tests / 'BULK-MANIFEST.sha256').write_text(digest + '  /original/unavailable/path\n')
            with patch.object(gate, 'ROOT', root), patch.object(gate, 'TESTS', tests):
                gate.verify_bulk_archive(archive, restore=True)
                self.assertEqual((tests / 'matrix.json').read_bytes(), source.read_bytes())
                archive.write_bytes(archive.read_bytes() + b'corrupt')
                with self.assertRaisesRegex(ValueError, 'SHA256'):
                    gate.verify_bulk_archive(archive)

    def test_replay_fingerprint_includes_runner(self):
        # Test the enumerated fingerprint without requiring retrieved bulk data.
        with patch.object(Path, 'read_bytes', return_value=b'test'), \
             patch.object(Path, 'read_text', return_value=''):
            self.assertIn('tests/sol-override-validation/gate_runtime.py', gate.replay_inputs())

    def test_stale_replay_inputs_are_rejected(self):
        # No regeneration of the old input hashes is allowed in production.
        with tempfile.TemporaryDirectory() as directory:
            tests = Path(directory)
            (tests / 'evidence').mkdir()
            (tests / 'evidence/serial-lakefile.toml').write_bytes(b'')
            with patch.object(gate, 'TESTS', tests), \
                 patch.object(gate, 'validate_serial_config'), \
                 patch.object(gate, 'replay_inputs', return_value={'changed': 'hash'}):
                with self.assertRaisesRegex(ValueError, 'inputs changed'):
                    gate.validate_replays([], {'inputs': {}})



if __name__ == '__main__':
    unittest.main()
