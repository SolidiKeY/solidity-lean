"""Guard silently omitted readonly originals and promoted lexical fixtures."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location('case_ledger',
    ROOT/'scripts/h62/item1/readonly-bind/case_ledger.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class LedgerRefusals(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Build a full792-shaped external fixture; CLI additionally authenticates
        # the real saved artifact by its pinned SHA256, never this synthetic one.
        cls.originals = {f'Solidity/Lowering/Readonly/{n}.lean': subprocess.check_output(
            ['git','show',m.BASE+f':Solidity/Lowering/Readonly/{n}.lean'], cwd=ROOT)
                         for n in m.overlay.HASHES}
        cls.frozen = {'base':m.BASE,'theorem_count':792,'declarations':[]}
        for path, raw in cls.originals.items():
            for found in m.DECL.finditer(m.census.mask(raw.decode())):
                if found[2]=='theorem':
                    cls.frozen['declarations'].append({'file':path,
                        'source_name':m.PREFIX+Path(path).stem+'.'+found[3],
                        'visibility':'private' if found[1] else 'public',
                        'signature_sha256':'synthetic-untrusted','variable_context':[]})
        while len(cls.frozen['declarations'])<792:
            i=len(cls.frozen['declarations'])
            cls.frozen['declarations'].append({'file':'synthetic','source_name':str(i)})

    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        paths=set(self.originals)|{v[1] for v in m.CASES.values()}|{'tests/h62/item1/readonly-bind/BindControls.lean'}
        for path in paths:
            target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes((ROOT/path).read_bytes())

    def run_ledger(self, frozen=None, originals=None):
        return m.account(self.root, frozen or self.frozen, originals or self.originals)

    def test_full_accounting_and_refusal_to_promote(self):
        result=self.run_ledger()
        self.assertEqual(len(result['rows']),25)
        self.assertEqual(result['counts']['removed-private-source-identity-unrestored'],3)
        self.assertFalse(result['full_goal_acceptance'])
        refs=[case['fixture'] for row in result['rows'] for case in row['cases'] if 'fixture' in case]
        self.assertEqual(len(refs),16)
        self.assertEqual(result['distinct_fixture_source_identities'],12)
        self.assertTrue(all(r['status']=='source-reference-only-not-current-kernel-acceptance' for r in refs))

    def test_original_membership(self):
        bad=copy.deepcopy(self.frozen);bad['declarations'].pop()
        with self.assertRaises(ValueError):self.run_ledger(frozen=bad)
        bad=copy.deepcopy(self.frozen);bad['declarations'][-1]=bad['declarations'][0]
        with self.assertRaises(ValueError):self.run_ledger(frozen=bad)

    def test_original_file_substitution(self):
        bad=dict(self.originals);first=next(iter(bad));bad[first]+=b'\n'
        with self.assertRaises(ValueError):self.run_ledger(originals=bad)

    def test_definition_or_statement_change(self):
        for relative, old, new in [
            ('Solidity/Lowering/Readonly/EnvironmentCredit.lean','state.events ++','[] ++'),
            ('Solidity/Lowering/Readonly/CaptureFailures.lean','(n + 1)','(n + 2)'),
            ('Solidity/Lowering/Readonly/CapturePhases.lean','private theorem get_plain','private theorem dropped')]:
            path=self.root/relative;raw=path.read_text();self.assertIn(old,raw)
            path.write_text(raw.replace(old,new,1))
            with self.assertRaises(ValueError):self.run_ledger()
            path.write_text(raw)

    def test_theorem_moved_outside_namespace(self):
        path=self.root/'tests/h62/item1/readonly-bind/PhaseControls.lean'
        namespace='Solidity.H62.ReadonlyBind.PhaseControls'
        path.write_text('namespace '+namespace+'\nend '+namespace+
                        '\ntheorem value_timeout : True := by trivial\n')
        with self.assertRaises(ValueError):
            m.fixture(self.root, str(path.relative_to(self.root)), namespace+'.value_timeout')

    def test_missing_commented_duplicate_or_foreign_fixture(self):
        path=self.root/'tests/h62/item1/readonly-bind/PhaseControls.lean';raw=path.read_text()
        for bad in [raw.replace('theorem value_timeout','theorem renamed'),
                    '/- '+raw+' -/', raw.replace('end Solidity.H62.ReadonlyBind.PhaseControls',
                                'theorem value_timeout : True := by trivial\nend Solidity.H62.ReadonlyBind.PhaseControls'),
                    raw.replace('namespace Solidity.H62','namespace Other.H62')]:
            path.write_text(bad)
            with self.assertRaises(ValueError):self.run_ledger()
        path.unlink()
        with self.assertRaises(OSError):self.run_ledger()


if __name__=='__main__':unittest.main()
