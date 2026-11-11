#!/usr/bin/env python3
"""Controls guard path-cache divergence, identity substitution and proof omission.

The Lean differential control compares the actual v2 helper with Lean 4.24's
original helper; it does not model either algorithm in Python. No public replay
is started. Supply the already built isolated candidate with --checker-source.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('va1_v2', HERE / 'trust-recheck-v2.py')
V = importlib.util.module_from_spec(spec)
spec.loader.exec_module(V)
R = V.recipe()
CHECKER = None
PACKET = None


class CandidateControls(unittest.TestCase):
    def test_reference_recipe_identity(self):
        self.assertEqual(R.REFERENCE.seconds, 300)
        self.assertEqual(R.REFERENCE.count, 267)
        self.assertFalse(R.REFERENCE.synthetic)

    def test_patch_identity(self):
        self.assertEqual(R.digest(HERE / 'trust-checker-v2.patch', R.clock() + 5), V.PATCH_SHA)

    def test_binding_rejects_wrong_schema_or_revision(self):
        from argparse import Namespace
        binding = dict(schema=1, base=V.BASE, patch_sha256=V.PATCH_SHA,
                       checker_revision='1' * 40, checker_sha256='2' * 64,
                       head='3' * 40, packet_sha256='4' * 64, manifest_sha256='5' * 64)
        mutations = [('schema', True), ('base', '0' * 40), ('patch_sha256', '0' * 64),
                     ('checker_revision', V.BASE), ('checker_revision', 'bad'),
                     ('checker_sha256', 'bad')]
        for key, value in mutations:
            with self.subTest(key=key, value=value), patch.object(R, 'load_json', return_value=dict(binding, **{key: value})):
                with self.assertRaises(R.InvalidInput):
                    V.validate_binding(R, Path('unused'), 'unused', Namespace(), R.clock() + 5)

    def test_binding_duplicate_json_is_refused(self):
        import hashlib
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'binding.json'
            path.write_text('{"schema":1,"schema":1}')
            sha = hashlib.sha256(path.read_bytes()).hexdigest()
            with self.assertRaises(R.InvalidInput):
                R.load_json(path, sha, R.clock() + 5)

    def test_valid_binding_and_late_refusals(self):
        import hashlib
        from argparse import Namespace
        from copy import deepcopy
        if CHECKER is None:
            self.fail('built candidate required')
        # Use the authentic already-preserved object identity, without replay.
        # This optional local control input stays outside the code branch.
        packet_path = PACKET
        if not packet_path.is_file():
            self.fail('supply preserved VA1 original packet; no skipped domain control')
        packet = json.loads(packet_path.read_text())
        original = packet['manifest_content']
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=CHECKER, text=True).strip()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = Namespace(checker_source=CHECKER, packet=root / 'packet', manifest=root / 'manifest')
            binding_path = root / 'binding'
            data = dict(schema=1, base=V.BASE, patch_sha256=V.PATCH_SHA,
                        checker_revision=revision, checker_sha256='2' * 64, head=packet['head'])
            def validate(manifest):
                config.manifest.write_text(json.dumps(manifest))
                supplied = dict(packet, manifest_content=manifest)
                config.packet.write_text(json.dumps(supplied))
                data['packet_sha256'] = hashlib.sha256(config.packet.read_bytes()).hexdigest()
                data['manifest_sha256'] = hashlib.sha256(config.manifest.read_bytes()).hexdigest()
                binding_path.write_text(json.dumps(data))
                sha = hashlib.sha256(binding_path.read_bytes()).hexdigest()
                return V.validate_binding(R, binding_path, sha, config, R.clock() + 10)
            profile = validate(original)
            self.assertEqual(profile.count, 267)
            self.assertEqual(profile.seconds, 300)
            self.assertEqual(profile.checker_revision, revision)
            for mutate in ('omit', 'hash', 'extra'):
                manifest = deepcopy(original)
                if mutate == 'omit': manifest['files'].pop()
                if mutate == 'hash': manifest['files'][0]['sha256'] = '0' * 64
                if mutate == 'extra': manifest['files'].append(dict(manifest['files'][0], path='Unexpected.olean'))
                with self.subTest(mutate=mutate), self.assertRaises(R.InvalidInput):
                    validate(manifest)
            digest = R.digest
            def modified_source(path, deadline):
                return '0' * 64 if Path(path) == CHECKER / 'Main.lean' else digest(path, deadline)
            with patch.object(R, 'digest', side_effect=modified_source), self.assertRaises(R.InvalidInput):
                validate(original)
            small = R.small
            def extra_source(command, cwd, deadline):
                if 'diff' in command: return 'Main.lean\nLean4Checker/Replay.lean\nUnexpected.lean'
                return small(command, cwd, deadline)
            with patch.object(R, 'small', side_effect=extra_source), self.assertRaises(R.InvalidInput):
                validate(original)

    def test_actual_candidate_kernel_rejects_invalid_proof(self):
        if CHECKER is None: self.fail('built candidate required')
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'KernelControl.lean'
            source.write_text("""import Lean4Checker.Replay
open Lean
-- Guards fresh replay rejecting a theorem body with the wrong universe/type.
unsafe def va1KernelControlV2 : IO Unit := do
  let prop := Expr.sort Level.zero
  let validType := Expr.forallE `p prop (.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let validProof := Expr.lam `p prop (.lam `h (.bvar 0) (.bvar 0) .default) .default
  let valid : ConstantInfo := .thmInfo { name := `controlValid, levelParams := [], type := validType, value := validProof }
  discard <| (← mkEmptyEnvironment).replay' (({} : Std.HashMap Name ConstantInfo).insert valid.name valid)
  let invalid : ConstantInfo := .thmInfo { name := `controlInvalid, levelParams := [], type := prop, value := prop }
  let rejected ← try
    discard <| (← mkEmptyEnvironment).replay' (({} : Std.HashMap Name ConstantInfo).insert invalid.name invalid)
    pure false
  catch _ => pure true
  unless rejected do throw <| IO.userError "invalid theorem body accepted"
  IO.println "V2_KERNEL_CONTROLS_PASS valid proof accepted, invalid proof rejected"
#eval va1KernelControlV2
""")
            result = subprocess.run(['lake', 'env', 'lean', '-j1', str(source)], cwd=CHECKER,
                                    capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('V2_KERNEL_CONTROLS_PASS', result.stdout)

    def test_differential_actual_lean_path_helpers(self):
        if CHECKER is None:
            self.fail('--checker-source is required; no skipped compatibility control')
        with tempfile.TemporaryDirectory(prefix='va1-v2-control-') as directory:
            root = Path(directory)
            a, b = root / 'MixedCase', root / 'other'
            a.mkdir(); b.mkdir()
            (a / 'Nested').mkdir()
            (a / 'A.olean').write_bytes(b'fixture')
            (a / 'Nested/B.olean').write_bytes(b'fixture')
            (b / 'A.olean').write_bytes(b'fixture')
            (root / 'alias').symlink_to(a, target_is_directory=True)
            roots = [a, b, root / 'alias', root / 'missing', root, a / 'Nested']
            files = [a / 'A.olean', a / 'Nested/B.olean', b / 'A.olean',
                     root / 'alias/A.olean', root / 'absent.olean']
            cases = []
            for file in files:
                for ordered in [roots, list(reversed(roots)), [root / 'missing', a], [b, a], [a, a], []]:
                    arr = '[' + ', '.join('System.FilePath.mk ' + json.dumps(str(p)) for p in ordered) + ']'
                    cases.append(f'  check (System.FilePath.mk {json.dumps(str(file))}) {arr}')
            source = root / 'Control.lean'
            source.write_text('''import Main
open Lean
-- Guards casing, nested roots, duplicate/ordered roots, symlinks and caught errors.
def check (file : System.FilePath) (roots : SearchPath) : IO Unit := do
  let cache ← IO.mkRef ({} : Std.HashMap String System.FilePath)
  let expected ← searchModuleNameOfFileName file roots
  for _ in [0:2] do
    let actual ← searchModuleV2 cache file roots
    unless expected == actual do
      throw <| IO.userError s!"path mismatch: {file}: {expected} != {actual}"
#eval do
''' + '\n'.join(cases) + '\n  IO.println "V2_PATH_EQUIVALENCE_PASS 30 cases, cold and warm cache"\n')
            result = subprocess.run(['lake', 'env', 'lean', '-j1', str(source)], cwd=CHECKER,
                                    capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('V2_PATH_EQUIVALENCE_PASS', result.stdout)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--checker-source', required=True, type=Path)
    parser.add_argument('--reference-packet', required=True, type=Path)
    args, rest = parser.parse_known_args()
    CHECKER = args.checker_source.resolve()
    PACKET = args.reference_packet.resolve()
    unittest.main(argv=[__file__, *rest])
