"""Tests of publish.py on a synthetic census (no extraction needed).

    python3 -B -m unittest discover -s scripts/lean-inventory -p 'test_*.py'
"""
import copy
import subprocess
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import publish as P  # noqa: E402

REV = 'a' * 40


def fam(name, verdict, counts, lines=10, decls=2, deps=None):
    f = {'family': name, 'area': 'Yul', 'verdict': verdict, 'lines': lines, 'decls': decls,
         'pseudo': 0, 'counts': dict(zip(('keep', 'ownerNeeded', 'orphan', 'unresolved'), counts)),
         'members': [[name.split(':', 1)[1] + 'A.lean', 'member', lines, decls, 0, None]],
         'timing': {}, 'witness': {}}
    if verdict == 'orphan':
        f['dependents'] = deps or {'lean': [], 'files': [], 'standalone': True}
    return f


def census(rev=REV, tree='t1', families=None):
    fams = families if families is not None else [
        fam('dir:Solidity/Yul/A/', 'keep', [1, 0, 1, 0]),
        fam('dir:Solidity/Yul/B/', 'orphan', [0, 0, 2, 0]),
        fam('dir:Solidity/Yul/C/', 'unresolved', [0, 1, 0, 1]),
    ]
    tv = {v: 0 for v in ('keep', 'ownerNeeded', 'orphan', 'unresolved')}
    td = dict(tv)
    for f in fams:
        tv[f['verdict']] += 1
        for v in td:
            td[v] += f['counts'][v]
    return {
        'schema': P.CENSUS_SCHEMA, 'version': 1, 'revision': rev, 'lean_tree_id': tree,
        'toolchain': 'leanprover/lean4:v4.24.0', 'goal': {'goal_decl': 'G'},
        'extraction': {'extractor_blob': 'e', 'graph_sha256': 'g'},
        'regenerate': ['cmd'], 'limitations': ['l'], 'scope': {'areas': ['Yul']},
        'recovery': {'revision': rev, 'command': 'git show'},
        'totals': {'families': len(fams), 'lines': sum(f['lines'] for f in fams),
                   'decls': sum(f['decls'] for f in fams), 'verdicts': tv, 'decl_verdicts': td},
        'areas': {}, 'certified_orphan_families': [f['family'] for f in fams
                                                   if f['verdict'] == 'orphan'],
        'families': fams,
    }


def raw(c):
    return (json.dumps(c) + '\n').encode()


class PublishTest(unittest.TestCase):
    def test_deterministic_and_consistent(self):
        r = raw(census())
        a = P.publish(r, 'c.json')
        self.assertEqual(a, P.publish(r, 'c.json'))
        pub = json.loads(a)
        self.assertEqual(P.consistent(pub), [])
        self.assertEqual(pub['census']['sha256'], P.sha256_bytes(r))
        self.assertEqual([o['family'] for o in pub['orphans']], ['dir:Solidity/Yul/B/'])
        self.assertEqual(pub['orphans'][0]['recovery'], REV)
        self.assertEqual(pub['authorization']['decision'], 'H721')

    def test_tamper_rejected(self):
        pub = json.loads(P.publish(raw(census()), 'c.json'))
        cases = []
        t = copy.deepcopy(pub)
        t['families'][0][2] = 'orphan'
        cases.append(t)
        t = copy.deepcopy(pub)
        t['totals']['verdicts']['keep'] += 1
        cases.append(t)
        t = copy.deepcopy(pub)
        t['orphans'][0]['dependents']['standalone'] = False
        cases.append(t)
        t = copy.deepcopy(pub)
        t['orphans'][0]['recovery'] = 'b' * 40
        cases.append(t)
        t = copy.deepcopy(pub)
        t['orphans'] = []
        cases.append(t)
        t = copy.deepcopy(pub)
        t['families'].reverse()
        cases.append(t)
        t = copy.deepcopy(pub)
        t['authorization']['census_options'] = {'reviewed_blanket': ['x']}
        cases.append(t)
        t = copy.deepcopy(pub)
        del t['totals']
        cases.append(t)
        for i, c in enumerate(cases):
            self.assertNotEqual(P.consistent(c), [], f'tamper case {i} accepted')

    def test_revalidation(self):
        old = census(rev='b' * 40, tree='t0')
        new_fams = [fam('dir:Solidity/Yul/A/', 'keep', [1, 0, 1, 0]),
                    fam('dir:Solidity/Yul/B/', 'unresolved', [0, 0, 1, 1]),
                    fam('dir:Solidity/Yul/D/', 'orphan', [0, 0, 1, 0])]
        pub = json.loads(P.publish(raw(census(families=new_fams)), 'c.json', raw(old), 'o'))
        rv = pub['revalidation']
        self.assertTrue(rv['drifted'])
        self.assertEqual(rv['verdict_changes'], [['dir:Solidity/Yul/B/', 'orphan', 'unresolved']])
        self.assertEqual(rv['removed_families'], [['dir:Solidity/Yul/C/', 'unresolved']])
        self.assertEqual(rv['added_families'], [['dir:Solidity/Yul/D/', 'orphan']])
        self.assertEqual(rv['orphans'], {'kept': [], 'no_longer_orphan': ['dir:Solidity/Yul/B/'],
                                         'new': ['dir:Solidity/Yul/D/']})
        self.assertEqual(P.consistent(pub), [])

    def test_check_detects_drift(self):
        with tempfile.TemporaryDirectory() as d:
            c, o = Path(d, 'c.json'), Path(d, 'out.json')
            c.write_bytes(raw(census()))
            self.assertEqual(P.main(['--census', str(c), '--output', str(o)]), 0)
            self.assertEqual(P.main(['--census', str(c), '--output', str(o), '--check']), 0)
            self.assertEqual(P.main(['--output', str(o), '--consistent']), 0)
            with self.assertRaises(SystemExit):
                P.main(['--output', str(o), '--verify-pins', d])
            c.write_bytes(raw(census(tree='t2')))
            self.assertEqual(P.main(['--census', str(c), '--output', str(o), '--check']), 1)

    def test_verify_pins(self):
        import sources as S
        with tempfile.TemporaryDirectory() as d:
            def git(*a):
                return subprocess.run(['git', '-C', d, *a], check=True, capture_output=True,
                                      text=True).stdout.strip()
            git('init', '-q')
            Path(d, 'Solidity/Yul/B').mkdir(parents=True)
            Path(d, 'Solidity/Yul/B/A.lean').write_text('def x := 1\n' * 10)
            Path(d, 'Solidity/Yul/C').mkdir(parents=True)
            Path(d, 'Solidity/Yul/C/U.lean').write_text('import Solidity.Yul.B.A\n')
            git('add', '-A')
            git('-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-qm', 'c')
            rev = git('rev-parse', 'HEAD')
            tree = S.lean_tree_id(S.tracked(d, rev))
            pub = json.loads(P.publish(raw(census(rev=rev, tree=tree)), 'c.json'))
            # U.lean imports the orphan family but the census claims it standalone.
            self.assertEqual(len(P.verify_pins(d, pub)), 1)
            self.assertIn('not a listed dependent', P.verify_pins(d, pub)[0])
            pub['orphans'][0]['dependents'] = {
                'lean': [['Solidity/Yul/C/U.lean', True, 0, 0]], 'files': [], 'standalone': False}
            self.assertEqual(P.verify_pins(d, pub), [])
            dropped = copy.deepcopy(pub)
            dropped['orphans'][0]['members'] = []
            self.assertIn('members differ', P.verify_pins(d, dropped)[0])
            pub['orphans'][0]['members'][0][2] = 11
            self.assertEqual(len(P.verify_pins(d, pub)), 1)
            pub['orphans'][0]['members'][0][0] = 'Solidity/Yul/B/Gone.lean'
            self.assertTrue(any('absent' in x for x in P.verify_pins(d, pub)))
            pub['census']['lean_tree_id'] = 'other'
            self.assertIn('differs', P.verify_pins(d, pub)[0])
            pub['recovery']['revision'] = 'c' * 40
            self.assertIn('cannot be read', P.verify_pins(d, pub)[0])

    def test_rejects_non_census(self):
        with self.assertRaises(SystemExit):
            P.publish(b'{"schema": "other"}', 'x.json')


if __name__ == '__main__':
    unittest.main()
