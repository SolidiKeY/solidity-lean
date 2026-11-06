"""Ensure runtime provisioning refuses unexpected paths without overwriting."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SCRIPT = ROOT/'scripts/h62/item4/generic-p10/provision_runtime.py'


class ProvisionTests(unittest.TestCase):
    def test_unexpected_outputs_and_parent_symlinks_preserved(self):
        real = Path(os.environ['GENERIC_P10_LEAN_EXE']).parent.parent
        for kind in ['output-symlink', 'output-file', 'parent-symlink']:
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                artifacts = root/'artifacts'
                artifacts.mkdir()
                victim = root/'victim'
                victim.write_text('preserve this exact content')
                output = artifacts/'runtime-env-test.sh'
                if kind == 'output-symlink': output.symlink_to(victim)
                elif kind == 'output-file': output.write_text('preserve existing environment')
                else:
                    outside = root/'outside'
                    outside.mkdir()
                    (artifacts/'evidence').symlink_to(outside, target_is_directory=True)
                result = subprocess.run([sys.executable, '-B', str(SCRIPT),
                    '--toolchain-root', str(real), '--artifacts', str(artifacts), '--report-name', 'test'],
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn(b'preserve', result.stdout)
                self.assertEqual(victim.read_text(), 'preserve this exact content')
                if kind == 'output-file': self.assertEqual(output.read_text(), 'preserve existing environment')
                if kind == 'parent-symlink': self.assertEqual(list(outside.iterdir()), [])


if __name__ == '__main__': unittest.main()
