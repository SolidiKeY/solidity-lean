#!/usr/bin/env python3
"""Guard against optimized Python accepting malformed lexical census metadata.

Synthetic metadata tests only: these establish no Lean witness or fidelity claim.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

DRIVER = Path(__file__).with_name('check_census.py')
SIGNATURE = 'theorem sample : True '


def fixture():
    return {
        'summary': {
            'frozen_source_verified': True, 'unresolved_references': [],
            'complete_interface_inventory': False, 'uncovered': 1,
            'simultaneous_witnesses_verified': 0, 'unterminated_signatures': [],
        },
        'declarations': [{
            'id': 'sample', 'statement_fidelity': 'UNELABORATED',
            'owner_status': 'UNCONFIRMED', 'signature_source': SIGNATURE,
            'signature_sha256': hashlib.sha256(SIGNATURE.encode()).hexdigest(),
        }],
    }


class CensusAcceptance(unittest.TestCase):
    def run_driver(self, data, optimized):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'census.json'
            path.write_text(json.dumps(data))
            return subprocess.run(
                [sys.executable, *(['-O'] if optimized else []), str(DRIVER), str(path)],
                capture_output=True, text=True,
            )

    def test_valid_metadata_and_explicit_null(self):
        for optimized in (False, True):
            for null in (False, True):
                data = fixture()
                if null:
                    data['declarations'][0]['signature_source'] = None
                    data['summary']['unterminated_signatures'] = ['sample']
                result = self.run_driver(data, optimized)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('CENSUS_REGRESSION_PASS', result.stdout)

    def test_every_metadata_refusal_survives_optimization(self):
        mutations = [
            ('summary', 'frozen_source_verified', False),
            ('summary', 'unresolved_references', ['missing']),
            ('summary', 'complete_interface_inventory', True),
            ('summary', 'uncovered', 0),
            ('summary', 'simultaneous_witnesses_verified', 1),
            ('summary', 'unterminated_signatures', ['unexpected']),
            ('row', 'statement_fidelity', 'VERIFIED'),
            ('row', 'owner_status', 'CONFIRMED'),
            ('row', 'signature_sha256', 'wrong'),
        ]
        for optimized in (False, True):
            for location, key, value in mutations:
                with self.subTest(optimized=optimized, key=key):
                    data = fixture()
                    target = data['summary'] if location == 'summary' else data['declarations'][0]
                    target[key] = value
                    result = self.run_driver(data, optimized)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertNotIn('CENSUS_REGRESSION_PASS', result.stdout)
            data = fixture()
            data['declarations'].append(copy.deepcopy(data['declarations'][0]))
            data['summary']['uncovered'] = 2
            result = self.run_driver(data, optimized)
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn('CENSUS_REGRESSION_PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()
