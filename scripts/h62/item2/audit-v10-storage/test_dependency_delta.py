#!/usr/bin/env python3
"""Small committed-tree integration controls for dependency routing, no Lean."""
from pathlib import Path
import subprocess
import tempfile
import unittest
import dependency_delta as d


class DependencyTests(unittest.TestCase):
    def test_import_comments_and_invalid_syntax(self):
        self.assertEqual(d.imports(b'/- import Solidity.Fake /- nested -/ -/\nimport Solidity.Real Init\n-- import Solidity.Other\n'), ['Init', 'Solidity.Real'])
        for bad in [b'import Solidity.Bad/Path\n', b'public import Solidity.A\n', b'import\n Solidity.A\n', b'/- unterminated']:
            with self.assertRaises(ValueError):
                d.imports(bad)

    def test_committed_delta_cycles_external_and_missing(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            def run(*args):
                return subprocess.check_output(['git', *args], cwd=root, stderr=subprocess.PIPE).decode().strip()
            run('init', '-q'); run('config', 'user.name', 'test'); run('config', 'user.email', 'test@example.invalid')
            (root/'Solidity').mkdir()
            (root/'Witness.lean').write_text('import Solidity.A\n')
            (root/'Solidity/A.lean').write_text('import Solidity.B Init\n')
            (root/'Solidity/B.lean').write_text('import Solidity.A\ndef value := 1\n')
            run('add', '.'); run('commit', '-qm', 'old'); old=run('rev-parse', 'HEAD')
            (root/'Solidity/B.lean').write_text('import Solidity.A Solidity.C\ndef value := 2\n')
            (root/'Solidity/C.lean').write_text('def extra := 0\n')
            run('add', '.'); run('commit', '-qm', 'new'); new=run('rev-parse', 'HEAD')
            # A live uncommitted file cannot supply or alter either committed tree.
            (root/'Solidity/B.lean').write_text('import Solidity.Uncommitted\n')
            row=d.compare(root, old, new, ['Witness.lean'])['rows'][0]
            self.assertEqual(row['changed_sources'], ['Solidity/B.lean'])
            self.assertEqual(row['added_sources'], ['Solidity/C.lean'])
            self.assertEqual(row['baseline']['external_imports'], ['Init'])
            self.assertEqual(row['kernel_status'], 'not-run; historical receipts unchanged')
            reverse=d.compare(root, new, old, ['Witness.lean'])['rows'][0]
            self.assertEqual(reverse['removed_sources'], ['Solidity/C.lean'])
            (root/'Witness.lean').write_text('import Solidity.Missing\n')
            run('add', '.');run('commit', '-qm', 'missing')
            with self.assertRaises(ValueError): d.compare(root, old, 'HEAD', ['Witness.lean'])
            with self.assertRaises(ValueError): d.compare(root, old, new, ['Witness.lean']*2)
            with self.assertRaises(ValueError): d.closure(root, old, '../Witness.lean')


if __name__ == '__main__':
    unittest.main()
