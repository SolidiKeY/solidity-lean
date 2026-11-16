"""Guard against false successes, wrong declaration identity and lost inventories."""
import importlib.util
import hashlib
from unittest.mock import Mock
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
sys.dont_write_bytecode = True
SCRIPT = pathlib.Path(__file__).with_name('process-totals.py')
spec = importlib.util.spec_from_file_location('totals', SCRIPT)
totals = importlib.util.module_from_spec(spec)
spec.loader.exec_module(totals)


class Controls(unittest.TestCase):
    def setUp(self):
        self.row = {'sourceId': 2, 'contract': 'C', 'sourceHash': 'hash'}
        self.proved = {**self.row, 'status': 'proved'}

    def test_exact_certified_result_is_required(self):
        self.assertEqual(totals.result_errors(self.row, {'results': [self.proved]}, 0, True), [])
        for payload in [{'results': []}, {'results': [self.proved, self.proved]},
                        {'results': [{**self.proved, 'sourceId': 3}]},
                        {'results': [{**self.proved, 'sourceHash': 'other'}]},
                        {'results': [{**self.proved, 'status': 'ready'}]},
                        {'results': [{**self.proved, 'verification': 'direct'}]},
                        {'results': [{**self.proved, 'preconditions': 'impossible'}]}]:
            with self.subTest(payload=payload):
                self.assertTrue(totals.result_errors(self.row, payload, 0, True))
        self.assertTrue(totals.result_errors(self.row, {'results': [self.proved]}, 1, True))
        self.assertTrue(totals.result_errors(self.row, {'results': [self.proved]}, 0, False))

    def test_setup_failure_retains_entire_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = pathlib.Path(directory)
            admission = folder/'admission.json'
            rows = [{**self.row, 'status': 'ready'}, {**self.row, 'status': 'unsupported'}]
            admission.write_text(json.dumps({'kind': 'u01-admission-only', 'attemptFinished': True,
                                             'results': rows, 'inputs': []}))
            work = folder/'new'
            run = subprocess.run([sys.executable, str(SCRIPT), '--admission', str(admission),
                                  '--work', str(work), '--repo', str(folder/'missing'),
                                  '--soljson', str(folder)], capture_output=True)
            self.assertEqual(run.returncode, 1)
            report = json.loads((work/'report.json').read_text())
            self.assertEqual([r['input'] for r in report['rows']], rows)
            self.assertFalse(report['attemptFinished'])
            self.assertFalse(report['allScheduledPassed'])
            self.assertFalse(report['sourceToVerdictBaseline'])
            self.assertTrue(report['errors'])

    def test_loaded_inventory_and_digest_share_a_snapshot(self):
        first = b'{"inventory": "first"}'
        second = b'{"inventory": "replacement"}'
        path = Mock()
        path.read_bytes.side_effect = [first, second]
        data, sha = totals.load_admission(path)
        self.assertEqual(data, {'inventory': 'first'})
        self.assertEqual(sha, hashlib.sha256(first).hexdigest())

    def test_existing_work_directory_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = pathlib.Path(directory)
            sentinel = folder/'report.json'
            sentinel.write_text('preserve')
            run = subprocess.run([sys.executable, str(SCRIPT), '--admission', str(folder/'missing'),
                                  '--work', str(folder), '--soljson', str(folder)], capture_output=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertEqual(sentinel.read_text(), 'preserve')


if __name__ == '__main__':
    unittest.main()
