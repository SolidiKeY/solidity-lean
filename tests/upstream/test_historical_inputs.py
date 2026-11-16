"""Regression checks for the pruned validation inputs."""
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import historical_inputs as history


class HistoricalInputsTest(unittest.TestCase):
    def test_each_missing_input_recovers_the_pinned_blob(self):
        for path, (commit, blob) in history.PINS.items():
            with self.subTest(path=path):
                self.assertFalse((history.ROOT / path).exists())
                data = history.read_historical(path)
                self.assertEqual(data, subprocess.check_output(
                    ['git', '-C', str(history.ROOT), 'show', f'{commit}:{path}']))
                self.assertEqual(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(), blob)

    def test_existing_file_takes_precedence(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            path.write_bytes(b'working file')
            with patch.object(history.subprocess, 'check_output', side_effect=AssertionError('unexpected Git call')):
                self.assertEqual(history.read_historical(path), b'working file')

    def test_unlisted_missing_file_is_not_recovered(self):
        with self.assertRaises(FileNotFoundError):
            history.read_historical('tests/upstream/baseline-20261028/not-a-pinned-input')

    def test_incorrect_git_bytes_are_rejected(self):
        path = next(iter(history.PINS))
        with patch.object(history.subprocess, 'check_output', return_value=b'incorrect'):
            with self.assertRaisesRegex(ValueError, 'blob mismatch'):
                history.read_historical(path)


if __name__ == '__main__':
    unittest.main()
