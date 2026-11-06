"""Guard equal-count census swaps and forged coverage without running Lean."""
import copy
import hashlib
import importlib.util
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[4] / 'scripts/h62/item2/audit-exact-verification/census_partition.py'
spec = importlib.util.spec_from_file_location('partition', path)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)


class PartitionTests(unittest.TestCase):
    def setUp(self):
        self.raw = [dict(name=n, module='M', signature='True', kernel_type_expr='T') for n in ('A', 'B')]
        self.old = [dict(r, coverage='named_source_h70_witness' if r['name']=='A' else 'uncovered_compiler_declaration') for r in self.raw]
        self.source = b'{"declarations":[{"name_candidate":"A"}]}'
        self.pin = hashlib.sha256(self.source).hexdigest()

    def check(self):
        return p.partition(self.raw, self.old, self.source, self.pin)

    def test_partition_is_not_witness(self):
        result = self.check()
        self.assertEqual(result['uncovered'], ['B'])
        self.assertEqual(result['witnesses_added'], 0)
        self.assertFalse(result['kernelValidated'])
        self.assertFalse(result['releaseClosed'])

    def test_equal_count_coverage_swap(self):
        self.old[0]['coverage'], self.old[1]['coverage'] = self.old[1]['coverage'], self.old[0]['coverage']
        with self.assertRaises(ValueError): self.check()

    def test_unknown_proof_label(self):
        self.old[0]['coverage'] = 'kernel_proved'
        with self.assertRaises(ValueError): self.check()

    def test_name_substitution_and_duplicate(self):
        for name in ('C', 'A'):
            with self.subTest(name=name):
                self.old[1]['name'] = name
                with self.assertRaises(ValueError): self.check()

    def test_all_kernel_fields_preserved(self):
        for key in ('module', 'signature', 'kernel_type_expr'):
            old = copy.deepcopy(self.old)
            self.old[0][key] = 'changed'
            with self.assertRaises(ValueError): self.check()
            self.old = old
        self.raw[0]['extra'] = 1
        self.old[0]['extra'] = True
        with self.assertRaises(ValueError): self.check()

    def test_digest_and_json_controls(self):
        for raw in (b'{"declarations":[],"declarations":[]}', b'{"declarations":NaN}', b'{"declarations":[{"name_candidate":false}]}'):
            self.source = raw
            self.pin = hashlib.sha256(raw).hexdigest()
            with self.assertRaises(ValueError): self.check()
        self.pin = '0'*64
        with self.assertRaises(ValueError): self.check()


if __name__ == '__main__': unittest.main()
