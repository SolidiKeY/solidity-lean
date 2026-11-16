import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts/h55/shared-fixtures/compare_extract_declarations.py'
EVIDENCE = pathlib.Path('/workspace/h55-shared-fixtures-evidence')


def lines(name):
    return (EVIDENCE / f'declarations-{name}.jsonl').read_text().splitlines()


class ComparatorTests(unittest.TestCase):
    def run_comparison(self, before, after):
        with tempfile.TemporaryDirectory() as directory:
            left, right = pathlib.Path(directory) / 'before', pathlib.Path(directory) / 'after'
            left.write_text('\n'.join(before) + '\n')
            right.write_text('\n'.join(after) + '\n')
            return subprocess.run(['python3', '-B', str(SCRIPT), str(left), str(right)],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode

    def test_real_inventories_pass(self):
        self.assertEqual(self.run_comparison(lines('baseline'), lines('changed')), 0)

    def test_changed_statement_and_axioms_are_rejected(self):
        before, after = lines('baseline'), lines('changed')
        for field, value in (('typeExpr', 'modified'), ('axioms', ['unapproved.axiom'])):
            mutated = list(after)
            i = next(i for i, line in enumerate(mutated) if line.startswith('H55_DECL '))
            row = json.loads(mutated[i].removeprefix('H55_DECL '))
            row[field] = value
            mutated[i] = 'H55_DECL ' + json.dumps(row)
            with self.subTest(field=field):
                self.assertEqual(self.run_comparison(before, mutated), 1)

    def test_missing_or_duplicate_records_are_rejected(self):
        before, after = lines('baseline'), lines('changed')
        i = next(i for i, line in enumerate(before) if line.startswith('H55_DECL '))
        self.assertEqual(self.run_comparison(before[:i] + before[i+1:], after), 2)
        self.assertEqual(self.run_comparison(before + [before[i]], after), 2)


if __name__ == '__main__':
    unittest.main()
