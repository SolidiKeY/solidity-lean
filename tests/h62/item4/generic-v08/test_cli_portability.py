"""Run the real census CLI outside the checkout, with external output paths."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT / 'scripts/h62/item4/generic-v08'


class CliPortability(unittest.TestCase):
    def test_audit_from_unrelated_directory(self):
        with tempfile.TemporaryDirectory(prefix='generic-v08-cli-') as directory:
            work = Path(directory)
            result = subprocess.run(
                [sys.executable, '-B', str(SCRIPTS / 'audit_current.py'),
                 '--output', 'evidence/report.json'],
                cwd=work, capture_output=True, text=True)
            report = json.loads((work / 'evidence/report.json').read_text())
            # An integrated proof-body change may legitimately trigger refusal;
            # portable operation must still report the real source-integrity state.
            self.assertEqual(result.returncode, 0 if report['original_integrity'] == 'pass' else 1)
            self.assertEqual(report['head'], subprocess.check_output(
                ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
            inventory_path = Path(report['current_inventory_path'])
            self.assertEqual(inventory_path.parent, work / 'evidence')
            inventory = json.loads(inventory_path.read_text())
            self.assertEqual(len(inventory['files']), report['current_file_count'])
            self.assertEqual(len(inventory['declarations']), report['current_declaration_count'])

    def test_reproducer_help_from_unrelated_directory(self):
        with tempfile.TemporaryDirectory(prefix='generic-v08-help-') as directory:
            result = subprocess.run(
                [sys.executable, '-B', str(SCRIPTS / 'reproduce-width.py'), '--help'],
                cwd=directory, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            for option in ('--toolchain', '--archive', '--output'):
                self.assertIn(option, result.stdout)


if __name__ == '__main__':
    unittest.main()
