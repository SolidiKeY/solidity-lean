#!/usr/bin/env python3
"""H534 controls guard source substitution and accidental replay admission.

These Python tests inspect the actual isolated candidate and exercise refusals;
they never run a checker, import public Lean modules or perform kernel replay.
Native metadata fixtures run separately through trust-recheck-v3.py.
"""
import argparse
from contextlib import redirect_stderr
import hashlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('va1_v3', HERE / 'trust-recheck-v3.py')
V = importlib.util.module_from_spec(spec)
spec.loader.exec_module(V)
CHECKER = None


def deadline():
    return time.clock_gettime(time.CLOCK_BOOTTIME) + 20


class MetadataControls(unittest.TestCase):
    def test_genuine_source_identity(self):
        revision = V.inspect_candidate(CHECKER, deadline())
        self.assertNotEqual(revision, V.BASE)
        self.assertEqual(len(V.SOURCES), 4)

    def test_patch_exactly_matches_committed_candidate(self):
        actual = subprocess.check_output(['git', '--no-replace-objects', 'diff', '--no-ext-diff',
                                          '--no-textconv', '--binary', '--unified=0', V.BASE, 'HEAD'], cwd=CHECKER)
        self.assertEqual(hashlib.sha256(actual).hexdigest(), V.PATCH_SHA)
        self.assertEqual(actual, (HERE / 'trust-checker-v3.patch').read_bytes())
        subprocess.run(['git', 'apply', '--unidiff-zero', '--reverse', '--check', str(HERE / 'trust-checker-v3.patch')],
                       cwd=CHECKER, check=True, capture_output=True)

    def test_only_one_replay_call_and_one_import_change_from_v2(self):
        # Reconstruct the frozen reviewed v2 bytes by reversing the exact two
        # edits. Do not require VA1's local v2 commit object: BASE plus the
        # committed self-contained patch is sufficient for reproduction.
        actual = (CHECKER / 'Lean4Checker/Replay.lean').read_text()
        added_import = 'import Lean.Util.FoldConsts\nimport Lean4Checker.FusedDepsV3'
        new_call = 'replayConstants (getUsedConstantsFusedV3 ci)'
        self.assertEqual(actual.count(added_import), 1)
        self.assertEqual(actual.count(new_call), 1)
        recovered = actual.replace(added_import, 'import Lean.Util.FoldConsts')
        recovered = recovered.replace(new_call, 'replayConstants ci.getUsedConstantsAsSet')
        self.assertEqual(hashlib.sha256(recovered.encode()).hexdigest(),
                         '4a04f64b19afd9ec36c268fbbd2ea81f293e9e64cb9bd7e63101fb6c8a01e245')
        self.assertIn('replayConstants ctor.getUsedConstantsAsSet', actual)
        self.assertEqual(V.digest(CHECKER / 'Main.lean'),
                         'd73db540ff418bba732561502bda86b1ea3f853cef39ede62ed5b386d81007bd')

    def test_each_modified_source_and_patch_substitution_is_refused(self):
        original = V.digest
        paths = [CHECKER / p for p in V.SOURCES] + [HERE / 'trust-checker-v3.patch']
        for target in paths:
            def corrupt(path):
                return '0' * 64 if Path(path) == target else original(path)
            with self.subTest(target=target), patch.object(V, 'digest', side_effect=corrupt):
                with self.assertRaises(V.Refused):
                    V.inspect_candidate(CHECKER, deadline())

    def test_dirty_or_unexpected_or_base_source_is_refused(self):
        original = V.call
        for mode in ('dirty', 'extra', 'base'):
            def altered(command, root, end, env=None):
                if mode == 'dirty' and 'status' in command: return ' M Main.lean\n'
                if mode == 'extra' and 'diff' in command: return '\n'.join(V.SOURCES) + '\nUnexpected.lean\n'
                if mode == 'base' and 'rev-parse' in command: return V.BASE + '\n'
                return original(command, root, end, env)
            with self.subTest(mode=mode), patch.object(V, 'call', side_effect=altered):
                with self.assertRaises(V.Refused):
                    V.inspect_candidate(CHECKER, deadline())

    def test_expired_deadline_refuses_before_running_a_command(self):
        with patch.object(V.subprocess, 'run') as run, self.assertRaises(V.Refused):
            V.call(['false'], CHECKER, time.clock_gettime(time.CLOCK_BOOTTIME) - 1)
        run.assert_not_called()

    def test_default_and_replay_cli_are_refused(self):
        for arguments in ([], ['--replay'], ['--fresh', 'Solidity.Theorems']):
            with self.subTest(arguments=arguments), redirect_stderr(io.StringIO()), patch.object(V, 'run_metadata') as run:
                with self.assertRaises(SystemExit) as error:
                    V.main(arguments)
                self.assertEqual(error.exception.code, 2)
                run.assert_not_called()

    def test_missing_opt_in_refuses_before_build_or_control(self):
        with patch.dict(os.environ, {}, clear=True), patch.object(V, 'call') as call:
            with self.assertRaises(V.Refused):
                V.run_metadata(CHECKER, Path('/unused'), deadline())
            call.assert_not_called()

    def test_guard_conditions_are_independently_required(self):
        valid = dict(TRUST_CLOUD_NO_SYSTEMD='1', TRUST_V3_METADATA_ONLY='1',
                     LEAN_NUM_THREADS='1', TRUST_BUDGET_RECORD='external-receipt')
        for key in valid:
            env = dict(valid); del env[key]
            with self.subTest(missing=key), patch.dict(os.environ, env, clear=True):
                with self.assertRaises(V.Refused): V.check_guards()
        with patch.dict(os.environ, valid, clear=True):
            with patch.object(V.resource, 'getrlimit', return_value=(-1, -1)):
                with self.assertRaises(V.Refused): V.check_guards()
            with patch.object(V.Path, 'read_text', return_value='header\nswapfile active\n'):
                with self.assertRaises(V.Refused): V.check_guards()

    def test_tool_identity_is_checked_before_build(self):
        with patch.object(V, 'check_guards'), patch.object(V, 'inspect_candidate', return_value='candidate'), \
             patch.object(V, 'digest', return_value='0' * 64), patch.object(V, 'call') as call:
            with self.assertRaises(V.Refused): V.run_metadata(CHECKER, Path('/unused'), deadline())
            call.assert_not_called()

    def test_metadata_control_has_no_replay_or_public_import(self):
        source = (CHECKER / 'Lean4Checker/FusedDepsV3Controls.lean').read_text()
        imports = [line for line in source.splitlines() if line.startswith('import ')]
        self.assertEqual(imports, ['import Lean4Checker.FusedDepsV3'])
        for forbidden in ('#eval', 'addDeclCore', 'importModules', 'mkEmptyEnvironment', '.replay\''):
            self.assertNotIn(forbidden, source)
        self.assertIn('negative-oracle', source)
        self.assertIn('V3_METADATA_CONTROLS_PASS', source)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker-source', required=True, type=Path)
    args, rest = parser.parse_known_args()
    CHECKER = args.checker_source.resolve()
    unittest.main(argv=[__file__, *rest])
