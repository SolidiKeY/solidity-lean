"""H76 static receipt/patch controls; never runs Lean or applies source patches."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SCRIPT = ROOT/'scripts/h62/item6/migrate-root-gate/review-delivery.py'
INPUTS = Path('/workspace/h76-inputs')


class DeliveryControls(unittest.TestCase):
    def test_complete_delivery_content_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'review'
            run = subprocess.run([sys.executable, '-B', str(SCRIPT), str(INPUTS), str(output)],
                                 capture_output=True, text=True, timeout=20)
            self.assertEqual(run.returncode, 0, run.stderr)
            review = json.loads((output/'review.json').read_text())
            self.assertEqual(len(review['receipts']), 10)
            self.assertTrue(review['hash_overlay']['fullpatch_manifest_result_bindings'])
            self.assertFalse(review['hash_overlay']['git_ancestry_verified'])
            self.assertFalse(review['hash_overlay']['patch_applied'])
            self.assertFalse(review['Lean_started'])

    def test_relative_input_from_other_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'review'
            relative = os.path.relpath(INPUTS, directory)
            run = subprocess.run([sys.executable, '-B', str(SCRIPT), relative, str(output)],
                                 cwd=directory, capture_output=True, text=True, timeout=20)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertTrue((output/'review.json').exists())

    def test_tampered_receipt_fails_before_output(self):
        with tempfile.TemporaryDirectory() as directory:
            inputs = Path(directory)/'inputs'
            inputs.mkdir()
            name = '8590f8229c-HANDOFF.md'
            (inputs/name).write_bytes((INPUTS/name).read_bytes()+b'changed')
            output = Path(directory)/'review'
            run = subprocess.run([sys.executable, '-B', str(SCRIPT), str(inputs), str(output)],
                                 capture_output=True, text=True, timeout=20)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn('receipt mismatch', run.stderr)
            self.assertFalse(output.exists())

    def test_wrong_hunk_context_is_rejected_in_memory(self):
        spec = importlib.util.spec_from_file_location('h76_review', SCRIPT)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        names = ['Solidity/Hash/Adaptive.lean', 'Solidity/Hash/CollisionBound.lean']
        originals = {name: subprocess.check_output(['git', 'show', module.BASE+':'+name], cwd=ROOT)
                     for name in names}
        before = {name: (ROOT/name).read_bytes() for name in names}
        lines = (INPUTS/'3f6f954038-hash-owner-overlay.patch').read_text().splitlines(True)
        first_hunk = next(i for i, line in enumerate(lines) if line.startswith('@@ '))
        context = next(i for i in range(first_hunk+1, len(lines)) if lines[i].startswith(' '))
        lines[context] = ' INVALID_BASE_CONTEXT\n'
        with self.assertRaisesRegex(ValueError, 'base context mismatch'):
            module.apply_in_memory(''.join(lines), originals)
        for name, original in originals.items():
            self.assertEqual((ROOT/name).read_bytes(), before[name])

    def test_base_applicability_preserves_real_index_and_sources(self):
        spec = importlib.util.spec_from_file_location('h76_base_review', SCRIPT)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        git_index = Path(subprocess.check_output(['git', 'rev-parse', '--git-path', 'index'], cwd=ROOT, text=True).strip())
        if not git_index.is_absolute():
            git_index = ROOT/git_index
        before_index = git_index.read_bytes()
        before_sources = {name: (ROOT/name).read_bytes() for name in ['Solidity/Hash/Adaptive.lean', 'Solidity/Hash/CollisionBound.lean']}
        patch = (INPUTS/'3f6f954038-hash-owner-overlay.patch').read_bytes()
        run = module.check_patch_at_base(patch)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(git_index.read_bytes(), before_index)
        for name, before in before_sources.items():
            self.assertEqual((ROOT/name).read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
