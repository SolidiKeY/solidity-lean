#!/usr/bin/env python3
"""Negative controls for migration acceptance decisions."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('compare', ROOT/'scripts/h62/item6/migrate-solkey/compare.py')
C = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C)


def baseline():
    return {'complete': True, 'modules': [{'module': 'M', 'exit': 0, 'stop': None}],
            'settings': {'threads': 1}, 'source_identity_sha256': 'fixed',
            'wall_seconds': 100, 'max_child_rss_kib': 100}


class AcceptanceControls(unittest.TestCase):
    def test_incomplete_and_failed_runs_are_rejected(self):
        for change in [{'complete': False}, {'modules': []},
                       {'modules': [{'module': 'M', 'exit': 1, 'stop': None}]}]:
            new = baseline(); new.update(change)
            with self.assertRaises(ValueError): C.compare(baseline(), new)

    def test_resource_and_input_drift_are_rejected(self):
        for change in [{'settings': {'threads': 2}}, {'source_identity_sha256': 'changed'},
                       {'modules': [{'module': 'different', 'exit': 0, 'stop': None}]}]:
            new = baseline(); new.update(change)
            with self.assertRaises(ValueError): C.compare(baseline(), new)

    def test_regression_thresholds_and_rss(self):
        old = baseline()
        for wall, rss, expected in [(100, 100, 'NO_REGRESSION'),
                                   (101, 100, 'ESCALATE_REGRESSION'),
                                   (111, 100, 'STOP_GT_10_PERCENT'),
                                   (99, 111, 'STOP_GT_10_PERCENT')]:
            new = copy.deepcopy(old); new.update(wall_seconds=wall, max_child_rss_kib=rss)
            self.assertEqual(C.compare(old, new)['status'], expected)


if __name__ == '__main__': unittest.main()
