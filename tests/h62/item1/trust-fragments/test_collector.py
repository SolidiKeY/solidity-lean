import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('collector', ROOT / 'scripts/h62/item1/trust-fragments/collect.py')
COLLECTOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COLLECTOR)


class CollectorTests(unittest.TestCase):
    def test_reproduces_frozen_audit(self):
        self.assertEqual(COLLECTOR.collect(COLLECTOR.FRAGMENTS), COLLECTOR.AUDIT.read_bytes())

    def test_missing_and_unexpected_fragments_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory)
            (path / '000-a.leanfrag').write_bytes(b'a')
            (path / '002-c.leanfrag').write_bytes(b'c')
            with self.assertRaises(ValueError):
                COLLECTOR.collect(path)
            (path / '002-c.leanfrag').unlink()
            (path / 'unexpected').write_bytes(b'x')
            with self.assertRaises(ValueError):
                COLLECTOR.collect(path)

    def test_baseline_census(self):
        data = COLLECTOR.collect(COLLECTOR.FRAGMENTS)
        self.assertEqual(len(re.findall(rb'^run_cmd do$', data, re.M)), 44)
        allowed = rb'^  let allowed : List Name := \[``propext, ``Classical.choice, ``Quot.sound\]$'
        self.assertEqual(len(re.findall(allowed, data, re.M)), 44)
        self.assertEqual(len(re.findall(rb'^#print axioms ', data, re.M)), 17)
        self.assertEqual(len(re.findall(rb'``Solidity\.', data)), 1380)
        for fragment in COLLECTOR.FRAGMENTS.iterdir():
            self.assertEqual(len(re.findall(rb'^run_cmd do$', fragment.read_bytes(), re.M)), 1)

    def test_migration_patch_matches_generated_output(self):
        patch = ROOT / 'scripts/h62/item1/trust-fragments/migration.patch'
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'TrustAudit.lean'
            result = subprocess.run(['patch', '--silent', '--output', str(output),
                                     str(COLLECTOR.AUDIT), str(patch)], capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(output.read_bytes(), COLLECTOR.MARKER + COLLECTOR.collect(COLLECTOR.FRAGMENTS))

    def test_check_rejects_mutation_and_missing_last_fragment(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory)
            for fragment in COLLECTOR.FRAGMENTS.iterdir():
                (path / fragment.name).write_bytes(fragment.read_bytes())
            files = sorted(path.iterdir())
            files[-1].unlink()
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/h62/item1/trust-fragments/collect.py'),
                                     '--fragments', str(path)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            files[-1].write_bytes(b'changed')
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/h62/item1/trust-fragments/collect.py'),
                                     '--fragments', str(path)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)

    def test_order_and_byte_preservation(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory)
            (path / '001-b.leanfrag').write_bytes(b'\x00b\n')
            (path / '000-a.leanfrag').write_bytes(b'a\r\n')
            self.assertEqual(COLLECTOR.collect(path), b'a\r\n\x00b\n')


if __name__ == '__main__':
    unittest.main()
