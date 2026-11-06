#!/usr/bin/env python3
"""Scanner controls: omit no assigned file, reject drift, ignore nested comments."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('census', ROOT/'scripts/h62/item6/migrate-solkey/census.py')
C = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C)


class CensusControls(unittest.TestCase):
    def test_nested_comments_and_string_delimiters(self):
        source = '/- import Fake.A /- nested -/ -/\nimport Real.B\n#eval "-- /-" -- comment\n'
        cleaned = C.uncomment(source)
        self.assertNotIn('Fake.A', cleaned)
        self.assertIn('import Real.B', cleaned)
        self.assertIn('"-- /-"', cleaned)
        self.assertEqual(source.count('\n'), cleaned.count('\n'))

    def test_all_five_modules_and_fixtures(self):
        data = C.census(ROOT)
        self.assertEqual({Path(m['source']).name for m in data['modules']}, {
            'ComputedRevert.lean', 'Constructors.lean', 'QuantifiedDiamond.lean',
            'ScopedFlip.lean', 'TestSuite.lean'})
        self.assertEqual(sum(len(m['fixtures']) for m in data['modules']), 11)
        self.assertEqual(sum(c['text'].startswith('theorem ') for m in data['modules'] for c in m['commands']), 3)

    def test_module_system_import_modifiers(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); (root/'Solidity/Solkey').mkdir(parents=True)
            (root/'Solidity/Solkey/Case.lean').write_text('public meta import all Lean.Elab.Command\nimport Lean.Data.Name Lean.Data.Json\n')
            data = C.census(root)
            self.assertEqual(data['modules'][0]['imports'], ['Lean.Elab.Command', 'Lean.Data.Name', 'Lean.Data.Json'])

    def test_command_line_locations(self):
        data = C.census(ROOT)
        for mod in data['modules']:
            lines = (ROOT/mod['source']).read_text().splitlines()
            for cmd in mod['commands']:
                self.assertEqual(lines[cmd['line']-1].strip(), cmd['text'])

    def test_source_fixture_and_dependency_mutations(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/'Solidity/Solkey').mkdir(parents=True)
            (root/'tests').mkdir()
            source = root/'Solidity/Solkey/Case.lean'
            dep = root/'Solidity/Dependency.lean'
            fixture = root/'tests/case.json'
            source.write_text('import Solidity.Dependency\nsolc_import "../../tests/case.json" hash 0x1 as Case\n#guard true\n')
            dep.write_text('def dependency := 1\n')
            fixture.write_text('{}')
            base = C.census(root)
            source.write_text(source.read_text().replace('#guard true', '#guard false'))
            self.assertNotEqual(base, C.census(root))
            source.write_text(source.read_text().replace('#guard false', '#guard true'))
            fixture.write_text('{"changed":true}')
            self.assertNotEqual(base, C.census(root))
            fixture.write_text('{}')
            dep.write_text('def dependency := 2\n')
            self.assertNotEqual(base, C.census(root))


if __name__ == '__main__': unittest.main()
