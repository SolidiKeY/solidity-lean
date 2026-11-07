#!/usr/bin/env python3
"""Acceptance tests for omission, private identity and frozen-drift failures."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('audit_census', Path(__file__).with_name('census.py'))
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)


class CensusAcceptance(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='h62-census-')
        self.root = Path(self.tmp.name)
        self.saved = census.ROOT, census.BASE
        census.ROOT = self.root
        (self.root/'docs/module-map').mkdir(parents=True)
        (self.root/'Solidity/Cases').mkdir(parents=True)
        (self.root/census.MAP).write_text('| '+chr(96)+'Cases/Fixture.lean'+chr(96)+' | fixture |\n')
        (self.root/'Solidity/Cases/Fixture.lean').write_text('''namespace Fixture
/- nested /- theorem hiddenInComment : False := no -/ ignored -/
variable {P : Prop}
theorem requires (h : P) : P := h
section Local
variable (n : Nat)
private theorem localOnly : n = n := rfl
end Local
theorem closed : True := True.intro
end Fixture
''')
        (self.root/'Solidity/Dependency.lean').write_text('def stable : Nat := 7\n')
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=AuditFixture', '-c', 'user.email=fixture@invalid',
                 'commit', '-qm', 'synthetic census baseline')
        census.BASE = self.git('rev-parse', 'HEAD').strip()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True, stderr=subprocess.DEVNULL)

    def tearDown(self):
        census.ROOT, census.BASE = self.saved
        self.tmp.cleanup()

    def test_exact_membership_and_private_identity(self):
        rows = census.census()['declarations']
        self.assertEqual([r['source_name'] for r in rows],
                         ['Fixture.requires', 'Fixture.localOnly', 'Fixture.closed'])
        self.assertEqual(rows[1]['variable_context'], ['variable {P : Prop}', 'variable (n : Nat)'])
        self.assertEqual(rows[2]['variable_context'], ['variable {P : Prop}'])
        self.assertIsNone(rows[1]['kernel_name'])
        self.assertEqual(rows[0]['kernel_name'], 'Fixture.requires')

    def test_changed_frozen_header_fails(self):
        p = self.root/'Solidity/Cases/Fixture.lean'
        p.write_text(p.read_text().replace('(h : P)', '(h : True)'))
        with self.assertRaisesRegex(ValueError, 'FROZEN_DRIFT'):
            census.census()

    def test_changed_unmapped_core_dependency_fails(self):
        (self.root/'Solidity/Dependency.lean').write_text('def stable : Nat := 8\n')
        with self.assertRaises(subprocess.CalledProcessError):
            census.census()

    def test_unresolved_module_map_fails(self):
        (self.root/census.MAP).write_text('| '+chr(96)+'Missing/*.lean'+chr(96)+' | not resolved |\n')
        with self.assertRaisesRegex(ValueError, 'unresolved module-map'):
            census.modules()

    def test_comments_strings_and_unterminated_input(self):
        text = '"theorem fake" /- outer /- theorem nested -/ -/\ntheorem real'
        masked = census.mask(text)
        self.assertEqual(masked.count('theorem'), 1)
        self.assertEqual(len(masked), len(text))
        with self.assertRaises(ValueError):
            census.mask('/- unterminated')


if __name__ == '__main__':
    unittest.main()
