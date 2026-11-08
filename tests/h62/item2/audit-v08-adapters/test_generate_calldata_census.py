"""Guard collector drift and out-of-scope generated diagnostic writes.

These are Python generator tests, not Lean witnesses or fidelity acceptance.
"""
import importlib.util
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[4]
SCRIPT = REPO / 'scripts/h62/item2/audit-v08-adapters/generate_calldata_census.py'
spec = importlib.util.spec_from_file_location('calldata_generator', SCRIPT)
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
TEMPLATE = (REPO / generator.TEMPLATE).read_text()


class Generator(unittest.TestCase):
    def prepare(self, folder):
        repo = Path(folder) / 'repo'
        path = repo / generator.TEMPLATE
        path.parent.mkdir(parents=True)
        path.write_text(TEMPLATE)
        return repo

    def run_generator(self, repo, name, optimized=False, expected=None):
        return subprocess.run(
            [sys.executable, *(['-O'] if optimized else []), str(SCRIPT),
             '--repo', str(repo), '--name', name,
             *(['--expect-sha256', expected] if expected is not None else [])],
            capture_output=True, text=True)

    def test_body_reused_verbatim_and_targets_exact(self):
        generated = generator.render(TEMPLATE)
        anchor = '  let constants := environment.constants.toList.mergeSort '
        self.assertEqual(generated[generated.index(anchor):], TEMPLATE[TEMPLATE.index(anchor):])
        self.assertEqual([line for line in generated.splitlines() if line.startswith('import ')],
                         ['import Lean', *('import ' + module for module in generator.MODULES)])
        self.assertEqual(generated.count('run_cmd do'), 1)
        self.assertEqual(generated.count(generator.MARKER), 4)
        for changed in (TEMPLATE.replace(anchor, '  let changed := '),
                        TEMPLATE.replace('collectAxioms name', 'changedAxioms name')):
            with self.assertRaises(ValueError):
                generator.render(changed)

    def test_stream_changes_only_enumeration_sort(self):
        line = '  let constants := environment.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)\n'
        sorted_source = generator.render(TEMPLATE)
        stream_source = generator.render(TEMPLATE, stream=True)
        self.assertEqual(stream_source, sorted_source.replace(line,
                         '  let constants := environment.constants.toList\n', 1).replace(
                         'Collector body is reused verbatim from P8StatementCensus.',
                         'P8 collector fields/filter are retained; only the global enumeration sort is omitted.'))
        changed = TEMPLATE.replace('fun a b => a.1.toString ≤ b.1.toString', 'fun _ _ => true')
        with self.assertRaisesRegex(ValueError, 'sort changed'):
            generator.render(changed, stream=True)

    def test_optional_result_shapes_keep_old_fields_and_filters(self):
        ordinary = generator.render(TEMPLATE, stream=True)
        shaped = generator.render(TEMPLATE, stream=True, result_shapes=True)
        self.assertNotIn('("result_shape", resultShape)', ordinary)
        self.assertIn('("result_shape", resultShape)', shaped)
        for token in ('environment.getModuleIdxFor? name', 'targets.findSome?',
                      'collectAxioms name', '("type_expr",', '("binders",'):
            self.assertEqual(ordinary.count(token), shaped.count(token))
        self.assertNotIn('body is reused verbatim', shaped)
        self.assertNotIn('only the global', shaped)
        self.assertIn('additional structural result fields', shaped)
        self.assertIn('result.isAppOfArity ``Eq 3', shaped)
        self.assertIn('args[1]! == args[2]!', shaped)
        for changed in (TEMPLATE.replace('let axioms ←', 'let altered ←'),
                        TEMPLATE.replace('let row :=', 'let alteredRow :=')):
            with self.assertRaisesRegex(ValueError, 'anchors changed'):
                generator.render(changed, result_shapes=True)

    def test_generation_is_exclusive_in_both_modes(self):
        for optimized in (False, True):
            with tempfile.TemporaryDirectory() as folder:
                repo = self.prepare(folder)
                result = self.run_generator(repo, 'Safe', optimized)
                self.assertEqual(result.returncode, 0, result.stderr)
                output = repo / generator.OUTPUT_ROOT / 'Safe.lean'
                self.assertEqual(output.read_text(), generator.render(TEMPLATE))
                again = self.run_generator(repo, 'Safe', optimized)
                self.assertNotEqual(again.returncode, 0)
                self.assertEqual(output.read_text(), generator.render(TEMPLATE))

    def test_pinned_hash_refuses_stale_materialization(self):
        for optimized in (False, True):
            with tempfile.TemporaryDirectory() as folder:
                repo = self.prepare(folder)
                refused = self.run_generator(repo, 'Pinned', optimized, '0' * 64)
                self.assertNotEqual(refused.returncode, 0)
                output = repo / generator.OUTPUT_ROOT / 'Pinned.lean'
                self.assertFalse(output.exists())
                expected = hashlib.sha256(generator.render(TEMPLATE).encode()).hexdigest()
                accepted = self.run_generator(repo, 'Pinned', optimized, expected)
                self.assertEqual(accepted.returncode, 0, accepted.stderr)
                self.assertEqual(hashlib.sha256(output.read_bytes()).hexdigest(), expected)

    def test_rejects_path_names(self):
        for optimized in (False, True):
            with tempfile.TemporaryDirectory() as folder:
                repo = self.prepare(folder)
                for name in ('../escape', '/absolute', 'bad.name'):
                    with self.subTest(name=name, optimized=optimized):
                        result = self.run_generator(repo, name, optimized)
                        self.assertNotEqual(result.returncode, 0)
                self.assertFalse((repo / generator.OUTPUT_ROOT).exists())

    def test_rejects_internal_and_external_symlink_redirection(self):
        for optimized in (False, True):
            for external in (False, True):
                with tempfile.TemporaryDirectory() as folder:
                    repo = self.prepare(folder)
                    output = repo / generator.OUTPUT_ROOT
                    destination = (Path(folder) if external else repo) / 'foreign'
                    destination.mkdir()
                    output.parent.mkdir(parents=True, exist_ok=True)
                    output.symlink_to(destination, target_is_directory=True)
                    result = self.run_generator(repo, 'Safe', optimized)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse((destination / 'Safe.lean').exists())


if __name__ == '__main__':
    unittest.main()
