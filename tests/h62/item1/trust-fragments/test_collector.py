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
sys.modules['collect'] = COLLECTOR
ACCEPT_SPEC = importlib.util.spec_from_file_location('accept_baseline', ROOT / 'scripts/h62/item1/trust-fragments/accept_baseline.py')
ACCEPT = importlib.util.module_from_spec(ACCEPT_SPEC)
ACCEPT_SPEC.loader.exec_module(ACCEPT)
sys.modules['accept_baseline'] = ACCEPT
CENSUS_SPEC = importlib.util.spec_from_file_location('census', ROOT / 'scripts/h62/item1/trust-fragments/census.py')
CENSUS = importlib.util.module_from_spec(CENSUS_SPEC)
CENSUS_SPEC.loader.exec_module(CENSUS)
sys.modules['census'] = CENSUS
FIXTURE_SPEC = importlib.util.spec_from_file_location('check_fixture', ROOT / 'scripts/h62/item1/trust-fragments/check_fixture.py')
FIXTURE = importlib.util.module_from_spec(FIXTURE_SPEC)
FIXTURE_SPEC.loader.exec_module(FIXTURE)
sys.modules['check_fixture'] = FIXTURE
TIMING_SPEC = importlib.util.spec_from_file_location('time_audit', ROOT / 'scripts/h62/item1/trust-fragments/time_audit.py')
TIMING = importlib.util.module_from_spec(TIMING_SPEC)
TIMING_SPEC.loader.exec_module(TIMING)


class CollectorTests(unittest.TestCase):
    def test_reproduces_frozen_audit(self):
        self.assertEqual(COLLECTOR.collect(COLLECTOR.FRAGMENTS), COLLECTOR.AUDIT.read_bytes())

    def test_timing_gate_boundary(self):
        self.assertFalse(TIMING.is_slow(100.0, 110.0))
        self.assertTrue(TIMING.is_slow(100.0, 110.001))
        with self.assertRaises(ValueError):
            TIMING.is_slow(0, 1)

    def test_census_accounts_for_each_original_occurrence(self):
        data = COLLECTOR.AUDIT.read_bytes()
        inventory = CENSUS.census(data)
        blocks = inventory['audit_blocks']
        names = [name for block in blocks for name in block['headlines']]
        self.assertEqual(len(blocks), 44)
        self.assertEqual(len(names), 1380)
        self.assertEqual(len(set(names)), 1373)
        self.assertEqual(len(inventory['imports']), 77)
        self.assertEqual(len(inventory['print_axioms']), 17)
        self.assertEqual(CENSUS.census(COLLECTOR.collect(COLLECTOR.FRAGMENTS)), inventory)
        with self.assertRaises(ValueError):
            CENSUS.census(data.replace(b'``Solidity.', b'``solidity.', 1))

    def test_pinned_acceptance_detects_matching_mutations(self):
        original = COLLECTOR.AUDIT.read_bytes()
        ACCEPT.accept(original, original, original)
        mutated = original.replace(b'``propext', b'``propExt', 1)
        self.assertNotEqual(mutated, original)
        with self.assertRaises(ValueError):
            ACCEPT.accept(mutated, mutated, mutated)
        with self.assertRaises(ValueError):
            ACCEPT.accept(original, mutated, original)
        with self.assertRaises(ValueError):
            ACCEPT.accept(original, original, mutated)
        with self.assertRaises(ValueError):
            ACCEPT.accept(original, original.replace(b'#print axioms ', b'--print axioms ', 1), original)

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
