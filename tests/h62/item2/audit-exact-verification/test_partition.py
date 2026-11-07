"""Guard equal-count census swaps and forged coverage without running Lean."""
import copy
import contextlib
import io
import tempfile
import hashlib
import importlib.util
import json
import os
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

    def pinned(self, raw=None, annotations=None, source=None, pins=None):
        data = {'compiler': json.dumps(self.raw).encode() if raw is None else raw,
                'annotations': json.dumps(self.old).encode() if annotations is None else annotations,
                'source': self.source if source is None else source}
        inventory = {k: hashlib.sha256(v).hexdigest() for k, v in data.items()}
        return p.partition_pinned(data['compiler'], data['annotations'], data['source'],
                                  inventory if pins is None else pins)

    def test_pinned_roundtrip_and_prior_label(self):
        self.old[0]['coverage'] = 'named_source_prior_witness'
        self.assertEqual(self.pinned(), self.check())

    def test_each_input_requires_external_pin(self):
        data = {'compiler': json.dumps(self.raw).encode(),
                'annotations': json.dumps(self.old).encode(), 'source': self.source}
        pins = {k: hashlib.sha256(v).hexdigest() for k, v in data.items()}
        for role in pins:
            bad = dict(pins, **{role: '0'*64})
            with self.subTest(role=role), self.assertRaises(ValueError):
                self.pinned(pins=bad)
        for bad in ({}, dict(pins, extra='0'*64), dict(pins, compiler=True)):
            with self.assertRaises(ValueError): self.pinned(pins=bad)

    def test_coordinated_metadata_drift(self):
        compiler = json.dumps(self.raw).encode()
        annotations = json.dumps(self.old).encode()
        pins = {'compiler': hashlib.sha256(compiler).hexdigest(),
                'annotations': hashlib.sha256(annotations).hexdigest(),
                'source': self.pin}
        self.raw[0]['signature'] = 'changed'
        self.old[0]['signature'] = 'changed'
        with self.assertRaises(ValueError): self.pinned(pins=pins)

    def test_duplicate_compiler_and_annotation_keys(self):
        for key in ('raw', 'annotations'):
            with self.subTest(role=key), self.assertRaises(ValueError):
                self.pinned(**{key: b'[{"name":"A","name":"B"}]'})

    def test_command_roundtrip_rejection_and_missing_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            values = {'compiler': json.dumps(self.raw).encode(),
                      'annotations': json.dumps(self.old).encode(), 'source': self.source}
            args = []
            for role, data in values.items():
                path = directory / (role + '.json')
                path.write_bytes(data)
                args += ['--' + role, str(path), '--' + role + '-sha256',
                         hashlib.sha256(data).hexdigest()]
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                self.assertEqual(p.main(args), 0)
            self.assertEqual(json.loads(out.getvalue()), self.check())
            self.assertEqual(err.getvalue(), '')
            (directory / 'compiler.json').write_bytes(b'[]')
            for missing in (False, True):
                if missing: (directory / 'compiler.json').unlink()
                out, err = io.StringIO(), io.StringIO()
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    self.assertEqual(p.main(args), 2)
                self.assertEqual(out.getvalue(), '')
                self.assertTrue(err.getvalue().startswith('CENSUS_METADATA_REJECT:'))

    def test_file_size_fifo_and_symlink_rejection(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            large = directory / 'large'
            with large.open('wb') as stream: stream.truncate(p.MAX_INPUT_BYTES + 1)
            fifo = directory / 'fifo'
            os.mkfifo(fifo)
            link = directory / 'link'
            link.symlink_to(large)
            for path in (large, fifo, link, directory):
                with self.subTest(path=path.name), self.assertRaises((OSError, ValueError)):
                    p.read_input(path)

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
        for raw in (b'{"declarations":[],"declarations":[]}', b'{"declarations":NaN}', b'{"declarations":[],"extra":1e999}', b'{"declarations":[{"name_candidate":false}]}'):
            self.source = raw
            self.pin = hashlib.sha256(raw).hexdigest()
            with self.assertRaises(ValueError): self.check()
        self.pin = '0'*64
        with self.assertRaises(ValueError): self.check()


if __name__ == '__main__': unittest.main()
