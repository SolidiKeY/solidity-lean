"""Guard silent loss of non-theorem audit signals; these are lexical tests only."""
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT / 'scripts/h62/item2/audit-v08-adapters'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('signals', SCRIPTS / 'declaration_signals.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class Signals(unittest.TestCase):
    def test_all_kinds_retained(self):
        self.assertEqual([r['keyword'] for r in module.signals('\n'.join(module.KINDS))], list(module.KINDS))

    def test_comments_strings_and_nested_comments(self):
        text = '-- theorem\n/- def /- axiom -/ structure -/\n"instance"\nclass C'
        self.assertEqual(module.signals(text), [dict(keyword='class', offset=text.index('class'), line=4, status='PENDING_LEXICAL_SIGNAL')])

    def test_identifier_boundaries(self):
        self.assertEqual(module.signals("mydef def' X.theorem structureName"), [])

    def test_quoted_syntax_remains_pending(self):
        rows = module.signals('`(def x := 0)')
        self.assertEqual(rows[0]['status'], 'PENDING_LEXICAL_SIGNAL')

    def test_duplicate_snapshot_refuses_before_git(self):
        with patch.object(module, 'frozen_blobs', return_value={}):
            with self.assertRaisesRegex(ValueError, 'Duplicate'):
                module.collect(ROOT, {'modules': [{'file': 'x'}, {'file': 'x'}]})

    def test_unknown_snapshot_module_refuses(self):
        with patch.object(module, 'frozen_blobs', return_value={}):
            with self.assertRaisesRegex(ValueError, 'Unknown'):
                module.collect(ROOT, {'modules': [{'file': 'missing'}]})

    def test_wrong_snapshot_hash_refuses(self):
        with patch.object(module, 'frozen_blobs', return_value={'x': 'blob'}):
            with patch.object(module.subprocess, 'check_output', return_value=b'def x := 0'):
                with self.assertRaisesRegex(ValueError, 'mismatch'):
                    module.collect(ROOT, {'modules': [{'file': 'x', 'sha256': 'wrong'}]})

    def test_unterminated_source_refuses(self):
        with self.assertRaises(ValueError):
            module.signals('/- def')


if __name__ == '__main__':
    unittest.main()
