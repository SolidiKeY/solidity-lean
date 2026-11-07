"""Guard missing-payload handoffs against erased failures, denominator drift and false acceptance.
Read-only metadata mutation controls; no runtime, Lean or performance execution.
"""
import copy
import importlib.util
import json
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location('metadata', Path(__file__).with_name('verify-handoff-metadata.py'))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class Controls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.handoff = json.loads(m.DEFAULT.read_bytes())
        cls.manifest = json.loads(m.git_bytes(m.HEAD, m.MANIFEST))

    def test_healthy_metadata_does_not_imply_payloads(self):
        report = m.verify(m.DEFAULT)
        self.assertEqual(report['runtimeGate'], 'pending')
        self.assertEqual(len(report['explicitGitSourcePinsVerified']), 2)
        self.assertTrue(all(not a['payloadInspected'] for a in report['artifacts']))
        self.assertFalse(report['execution'])

    def test_independent_metadata_drift(self):
        for field in ['sourceBuildHead', 'binaries', 'archives', 'gates']:
            with self.subTest(field=field):
                h = copy.deepcopy(self.handoff)
                h[field] = None
                with self.assertRaises(ValueError):
                    m.check_metadata(h, self.manifest)

    def test_coordinated_false_acceptance(self):
        changes = [
            ('runtimeGate', lambda x: 'pass', 'runtime hold'),
            ('addressControlsPerBackend', lambda x: {**x, 'unsupported': 0}, 'address denominator'),
            ('retainedSTOPs', lambda x: {**x, 'nativeMedianPercent': 0}, 'performance holds'),
            ('gates', lambda xs: [{**g, 'status': 'pass', 'exitCode': 0} for g in xs], 'gate failure'),
            ('gates', lambda xs: [xs[0]] + xs[:-1], 'gate denominator/identity'),
            ('gates', lambda xs: [{**g, 'exitCode': 1} if i == 0 else g
                                 for i, g in enumerate(xs)], 'status/exit'),
            ('archives', lambda xs: [xs[0]] + xs[:-1], 'archive denominator/identity'),
            ('archives', lambda xs: [{**a, 'path': '/workspace/solidity-lean/../bad'}
                                    if i == 0 else a for i, a in enumerate(xs)], 'unsafe artifact'),
        ]
        for field, change, marker in changes:
            with self.subTest(field=field, marker=marker):
                h, doc = copy.deepcopy(self.handoff), copy.deepcopy(self.manifest)
                doc[field] = change(doc[field])
                if field in h:
                    h[field] = copy.deepcopy(doc[field])
                with self.assertRaisesRegex(ValueError, marker):
                    m.check_metadata(h, doc)


if __name__ == '__main__':
    unittest.main()
