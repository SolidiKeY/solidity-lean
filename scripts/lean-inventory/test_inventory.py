"""Boundary tests: classifier rules, lexical helpers, and an end-to-end fixture repository
run through inventory.py and the independent checker with tampering negative controls.

Run: python3 -B -m unittest discover -s scripts/lean-inventory -p 'test_*.py'
"""
import copy
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sources as S  # noqa: E402
import classify as CL  # noqa: E402
import inventory as INV  # noqa: E402
import checker as CH  # noqa: E402


def facts(decls, edges, consumers, gaps=(), roles=None, families=None):
    """Synthetic facts: declaration `F.x` lives in module `F` (role from `roles`)."""
    roles = roles or {}
    families = families or {}
    decl_module = {d: d.split('.')[0] for d in decls}
    info = {}
    for m in set(decl_module.values()) | set(families):
        info[m] = {'family': families.get(m, m), 'role': roles.get(m, 'member'), 'area': 'x'}
    return CL.Facts(set(decls), decl_module, info,
                    {k: set(v) for k, v in edges.items()}, consumers, list(gaps))


def verdicts(f):
    rows, fams, _ = CL.classify(f)
    return {d: r['verdict'] for d, r in rows.items()}, {k: CL.family_verdict(v) for k, v in fams.items()}, rows


class ClassifierTests(unittest.TestCase):
    def test_real_use_is_keep_but_blanket_and_import_are_not(self):
        f = facts(['A.a', 'B.b'], {}, {'t': {'kind': 'test', 'roots': {'A.a'}},
                                       'root': {'kind': 'blanket', 'roots': {'B.b'}}})
        v, fam, rows = verdicts(f)
        self.assertEqual(v, {'A.a': 'keep', 'B.b': 'orphan'})
        self.assertEqual(rows['A.a']['consumer'], 't')

    def test_transitive_path_outside_the_areas(self):
        # `Mid.m` is not an in-scope declaration but carries the use.
        f = facts(['A.a'], {'Mid.m': {'A.a'}}, {'t': {'kind': 'goalProof', 'roots': {'Mid.m'}}})
        v, _, rows = verdicts(f)
        self.assertEqual(v['A.a'], 'keep')
        self.assertEqual((rows['A.a']['root'], rows['A.a']['path']), ('Mid.m', ['A.a']))

    def test_own_controls_demand_is_owner_needed(self):
        f = facts(['A.a', 'AC.c'], {'AC.c': {'A.a'}}, {},
                  roles={'AC': 'controls'}, families={'AC': 'A', 'A': 'A'})
        v, fam, rows = verdicts(f)
        self.assertEqual(v['A.a'], 'ownerNeeded')
        self.assertEqual(rows['A.a']['owner'], 'A')
        self.assertEqual(fam['A'], 'ownerNeeded')

    def test_cross_family_controls_demand_names_the_demanding_family(self):
        f = facts(['A.a', 'BC.c'], {'BC.c': {'A.a'}}, {},
                  roles={'BC': 'controls'}, families={'BC': 'B', 'A': 'A'})
        v, fam, rows = verdicts(f)
        self.assertEqual((v['A.a'], rows['A.a']['owner'], rows['A.a']['seed']),
                         ('ownerNeeded', 'B', 'BC.c'))

    def test_independently_used_control_becomes_keep(self):
        f = facts(['A.a', 'AC.c'], {'AC.c': {'A.a'}}, {'cli': {'kind': 'cli', 'roots': {'AC.c'}}},
                  roles={'AC': 'controls'}, families={'AC': 'A', 'A': 'A'})
        v, fam, _ = verdicts(f)
        self.assertEqual((v['AC.c'], v['A.a'], fam['A']), ('keep', 'keep', 'keep'))

    def test_blanket_controls_runner_is_not_keep(self):
        f = facts(['A.a', 'AC.c'], {'AC.c': {'A.a'}},
                  {'all-controls': {'kind': 'ownControls', 'roots': {'AC.c'}}},
                  roles={'AC': 'controls'}, families={'AC': 'A', 'A': 'A'})
        _, fam, _ = verdicts(f)
        self.assertEqual(fam['A'], 'ownerNeeded')

    def test_cycle_without_demand_is_orphan(self):
        f = facts(['C.p', 'C.q'], {'C.p': {'C.q'}, 'C.q': {'C.p'}},
                  {'b': {'kind': 'blanket', 'roots': {'C.p'}}})
        v, fam, _ = verdicts(f)
        self.assertEqual((v['C.p'], v['C.q'], fam['C']), ('orphan', 'orphan', 'orphan'))

    def test_targeted_gap_makes_its_closure_unresolved_only(self):
        gap = {'source': ('use', None), 'targets': ['D.i'], 'reason': 'implicit', 'class': 'g'}
        f = facts(['D.i', 'D.d', 'E.e'], {'D.i': {'D.d'}}, {}, gaps=[gap])
        v, fam, rows = verdicts(f)
        self.assertEqual((v['D.i'], v['D.d'], v['E.e']), ('unresolved', 'unresolved', 'orphan'))
        self.assertEqual((rows['D.d']['target'], rows['D.d']['path']), ('D.i', ['D.d']))

    def test_untargeted_gap_blocks_every_absence(self):
        gap = {'source': ('root', None), 'targets': None, 'reason': 'unknown', 'class': 'g'}
        f = facts(['A.a', 'B.b'], {}, {'t': {'kind': 'test', 'roots': {'A.a'}}}, gaps=[gap])
        v, _, _ = verdicts(f)
        self.assertEqual(v, {'A.a': 'keep', 'B.b': 'unresolved'})

    def test_gap_keeps_controls_demand_unresolved(self):
        gap = {'source': ('use', None), 'targets': ['A.a'], 'reason': 'implicit', 'class': 'g'}
        f = facts(['A.a', 'AC.c'], {'AC.c': {'A.a'}}, {}, gaps=[gap],
                  roles={'AC': 'controls'}, families={'AC': 'A', 'A': 'A'})
        v, _, _ = verdicts(f)
        self.assertEqual(v['A.a'], 'unresolved')

    def test_family_aggregation(self):
        fv = CL.family_verdict
        self.assertEqual(fv(['keep', 'orphan', 'unresolved']), 'keep')
        self.assertEqual(fv(['orphan', 'unresolved', 'ownerNeeded']), 'unresolved')
        self.assertEqual(fv([]), 'unresolved')
        self.assertEqual(fv(['orphan', 'ownerNeeded']), 'ownerNeeded')
        self.assertEqual(fv(['orphan', 'orphan']), 'orphan')


class LexicalTests(unittest.TestCase):
    def test_grouping_keeps_controls_triples_out_of_directory_families(self):
        sib = {'Solidity/Yul/A.lean', 'Solidity/Yul/AControls.lean', 'Solidity/Yul/APins.lean',
               'Solidity/Yul/B.lean', 'Solidity/Yul/Sub/Controls.lean'}
        self.assertEqual(S.family_of('Solidity/Yul/A.lean', sib), ('triple:Solidity/Yul/A', 'member'))
        self.assertEqual(S.family_of('Solidity/Yul/APins.lean', sib), ('triple:Solidity/Yul/A', 'pins'))
        self.assertEqual(S.family_of('Solidity/Yul/B.lean', sib), ('dir:Solidity/Yul/', 'member'))
        self.assertEqual(S.family_of('Solidity/Yul/Sub/Controls.lean', sib),
                         ('dir:Solidity/Yul/Sub/', 'controls'))
        for p in sib:
            self.assertEqual(S.family_of(p, sib), CH._group(p, sib))

    def test_command_classification(self):
        text = 'theorem t : True := by\n  trivial\n#guard 1 = 1\nexample : True := trivial\n' \
               'attribute [simp] t\nfoo_command x\n'
        starts = S.command_starts(text)
        self.assertEqual({k: S.classify_command(v) for k, v in starts.items()},
                         {1: 'declaration-or-scope', 3: 'consumer', 4: 'consumer',
                          5: 'declaration-or-scope', 6: 'unclassified'})

    def test_header_imports_stop_at_the_first_command(self):
        self.assertEqual(S.header_imports('import A\n-- c\nimport B.C\n\nnamespace X\nimport D\n'),
                         ['A', 'B.C'])

    def test_template_imports_keep_dynamic_prefixes(self):
        self.assertEqual(S.template_imports("w(`import Solidity.Tools.${p?'A':'B'}\\n#x`)"),
                         {'Solidity.Tools*'})
        self.assertEqual(S.template_imports('"import Solidity.Frontend.Testing\\n"'),
                         {'Solidity.Frontend.Testing'})

    def test_attributes(self):
        text = '@[simp] theorem a : True := trivial\n@[inline] def b := 1\nattribute [grind] c\n'
        self.assertEqual(S.attributed_heads(text), {1})
        self.assertEqual(S.attribute_commands(text), {'c'})


# ------------------------------------------------------------- fixture repo ----

FILES = {
    'lean-toolchain': 'leanprover/lean4:v4.24.0\n',
    'Solidity.lean': ''.join(f'import Solidity.{m}\n' for m in (
        'Backend.A', 'Backend.AControls', 'Yul.B', 'Lowering.C', 'Frontend.D',
        'SolcValidation.E', 'Source.F', 'Optimizer.G', 'Calc.Mid', 'Goals')),
    'SolidityExamples.lean': 'import Solidity.Examples.T\n',
    'Solidity/Backend/A.lean': 'def a1 := 1\ndef a2 := 2\n',
    'Solidity/Backend/AControls.lean': 'import Solidity.Backend.A\ndef c := a2\n#guard b1 = 1\n',
    'Solidity/Yul/B.lean': 'def b1 := 1\n',
    'Solidity/Lowering/C.lean': 'mutual\ndef p := q\ndef q := p\nend\n',
    'Solidity/Frontend/D.lean': 'instance i : Inhabited Nat := ⟨d1⟩\ndef d1 := 1\n',
    'Solidity/SolcValidation/E.lean': 'def e1 := 1\n',
    'Solidity/Source/F.lean': '-- no declarations\n',
    'Solidity/Optimizer/G.lean': 'def g1 := 1\n',
    'Solidity/Calc/Mid.lean': 'def m := a1\n',
    'Solidity/Goals.lean': 'def goal : Prop := True\n',
    'Solidity/Examples/T.lean': 'import Solidity.Calc.Mid\ntheorem t1 : m = m := rfl\n',
    'tests/x.lean': 'import Solidity.SolcValidation.E\n#eval e1\n',
}
CONSTS = [  # module, name, kind, refs, range, flags
    ('Solidity.Backend.A', 'Solidity.Backend.A.a1', 'def', [], [1, 1], {}),
    ('Solidity.Backend.A', 'Solidity.Backend.A.a2', 'def', [], [2, 2], {}),
    ('Solidity.Backend.AControls', 'Solidity.Backend.AControls.c', 'def',
     ['Solidity.Backend.A.a2'], [2, 2], {}),
    ('Solidity.Yul.B', 'Solidity.Yul.B.b1', 'def', [], [1, 1], {}),
    ('Solidity.Lowering.C', 'Solidity.Lowering.C.p', 'def', ['Solidity.Lowering.C.q'], [2, 2], {}),
    ('Solidity.Lowering.C', 'Solidity.Lowering.C.q', 'def', ['Solidity.Lowering.C.p'], [3, 3], {}),
    ('Solidity.Frontend.D', 'Solidity.Frontend.D.i', 'def', ['Solidity.Frontend.D.d1'], [1, 1],
     {'inst': True}),
    ('Solidity.Frontend.D', 'Solidity.Frontend.D.d1', 'def', [], [2, 2], {}),
    ('Solidity.Frontend.D', 'Solidity.Frontend.D.d1.eq_1', 'theorem', ['Solidity.Frontend.D.d1'],
     None, {}),
    ('Solidity.SolcValidation.E', 'Solidity.SolcValidation.E.e1', 'def', [], [1, 1], {}),
    ('Solidity.Optimizer.G', 'Solidity.Optimizer.G.g1', 'def', [], [1, 1], {}),
    ('Solidity.Calc.Mid', 'Solidity.Calc.Mid.m', 'def', ['Solidity.Backend.A.a1'], [1, 1], {}),
    ('Solidity.Goals', 'Solidity.Goals.goal', 'def', [], [1, 1], {}),
    ('Solidity.Examples.T', 'Solidity.Examples.T.t1', 'theorem', ['Solidity.Calc.Mid.m'], [2, 2], {}),
]
ANON = {'Solidity.Backend.AControls': [[3, 'Solidity.Yul.B.b1']]}
BUILD_LOG = ('✔ [1/3] Built Solidity.Backend.A (1.5s)\n✔ [2/3] Fetched Solidity.Yul.B\n'
             '✔ [3/3] Built Solidity.Optimizer.G (850ms)\n')


def make_fixture(root):
    root = Path(root)
    for p, t in FILES.items():
        (root / p).parent.mkdir(parents=True, exist_ok=True)
        (root / p).write_text(t)
    env = dict(os.environ, GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t', GIT_COMMITTER_NAME='t',
               GIT_COMMITTER_EMAIL='t@t')
    for cmd in (['init', '-q'], ['add', '-A'], ['commit', '-qm', 'fixture']):
        subprocess.run(['git', '-C', str(root), *cmd], check=True, env=env)
    rev = S.resolve(root, 'HEAD')
    cdir = root / INV.CACHE_ROOT / rev
    cdir.mkdir(parents=True)
    recs = [{'r': 'header', 'lean': '4.24.0', 'githash': 'x'}]
    mods = sorted({c[0] for c in CONSTS} | {'Solidity.Source.F'})
    recs += [{'r': 'module', 'g': 'lib', 'm': m, 'imports': []} for m in mods]
    for m, n, k, refs, rng, flags in CONSTS:
        r = {'r': 'const', 'g': 'lib', 'm': m, 'n': n, 'k': k, 'refs': refs, **flags}
        if rng:
            r['range'] = rng
        recs.append(r)
    recs.append({'r': 'goal', 'g': 'lib', 'decl': 'Solidity.Goals.goal',
                 'proof': 'Solidity.Yul.B.b1', 'plan': 'x', 'deps': []})
    recs.append({'r': 'end'})
    with gzip.open(cdir / 'graph.jsonl.gz', 'wt') as f:
        for r in recs:
            f.write(json.dumps(r, sort_keys=True) + '\n')
    (cdir / 'anon.json').write_text(json.dumps(ANON, sort_keys=True))
    (cdir / 'build.log').write_text(BUILD_LOG)
    ident = {'revision': rev, 'lean_tree_id': S.lean_tree_id(S.tracked(root, rev)),
             'toolchain': 'leanprover/lean4:v4.24.0', 'lean_version': '4.24.0',
             'lean_githash': 'x', 'extractor_blob': 'x', 'groups': {'lib': ['Solidity']},
             'olean_digest': 'x', 'ilean_digest': 'x', 'missing_compiled': [],
             'build_command': 'build', 'extract_command': 'extract'}
    for name, key in (('graph.jsonl.gz', 'graph_sha256'), ('anon.json', 'anon_sha256'),
                      ('build.log', 'build_log_sha256')):
        ident[key] = INV.sha256_file(cdir / name)
    (cdir / 'identity.json').write_text(json.dumps(ident))
    return rev


class FixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp()
        cls.rev = make_fixture(cls.tmp)
        cls.out = Path(cls.tmp) / 'inv.json'
        cls.text = INV.render(INV.build(INV.Inputs(cls.tmp, cls.rev)))
        cls.inv = json.loads(cls.text)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp)

    def fam(self, name):
        return next(f for f in self.inv['families'] if f['family'] == name)

    def test_every_area_and_module_is_covered(self):
        paths = sorted(m[0] for f in self.inv['families'] for m in f['members'])
        self.assertEqual(paths, sorted(p for p in FILES if S.area_of(p)))
        self.assertEqual(set(self.inv['areas']), set(S.AREAS))

    def test_verdicts(self):
        got = {f['family']: f['verdict'] for f in self.inv['families']}
        self.assertEqual(got, {
            'triple:Solidity/Backend/A': 'keep',          # a1 kept, a2 controls-only: mixed
            'dir:Solidity/Yul/': 'keep',                  # goal proof
            'dir:Solidity/Lowering/': 'orphan',           # cycle without demand
            'dir:Solidity/Frontend/': 'unresolved',       # instance: implicit-use gap
            'dir:Solidity/SolcValidation/': 'unresolved',  # unextracted tests/x.lean
            'dir:Solidity/Source/': 'unresolved',         # no declarations
            'dir:Solidity/Optimizer/': 'orphan'})
        a = self.fam('triple:Solidity/Backend/A')
        self.assertEqual(a['counts'], {'keep': 1, 'ownerNeeded': 3, 'orphan': 0, 'unresolved': 0})
        self.assertEqual(a['pseudo'], 1)
        # The keep path runs through `Calc.Mid`, outside the seven areas.
        self.assertEqual(a['witness']['root'], 'Solidity.Examples.T.t1')
        self.assertEqual(a['witness']['path'], ['Solidity.Calc.Mid.m', 'Solidity.Backend.A.a1'])
        self.assertEqual(self.fam('dir:Solidity/Frontend/')['decls'], 2)  # eq_1 folded into d1
        self.assertEqual(self.inv['certified_orphan_families'],
                         ['dir:Solidity/Lowering/', 'dir:Solidity/Optimizer/'])

    def test_timing_records(self):
        rows = {m[0]: m[5] for f in self.inv['families'] for m in f['members']}
        self.assertEqual(rows['Solidity/Backend/A.lean'], 1500)
        self.assertEqual(rows['Solidity/Optimizer/G.lean'], 850)
        self.assertIsNone(rows['Solidity/Yul/B.lean'])

    def test_regeneration_is_byte_identical_and_checker_accepts(self):
        again = INV.render(INV.build(INV.Inputs(self.tmp, self.rev)))
        self.assertEqual(again, self.text)
        self.assertEqual(CH.check(Path(self.tmp), self.inv), [])

    def tampered(self, edit):
        inv = copy.deepcopy(self.inv)
        edit(inv)
        return CH.check(Path(self.tmp), inv)

    def test_tampering_is_rejected(self):
        cases = {
            'witness path': lambda i: self.fam_in(i, 'triple:Solidity/Backend/A')['witness'].update(
                path=['Solidity.Backend.A.a2']),
            'verdict': lambda i: self.fam_in(i, 'dir:Solidity/Frontend/').update(verdict='orphan'),
            'dropped module': lambda i: i['families'].pop(),
            'line count': lambda i: i['families'][0]['members'][0].__setitem__(2, 99),
            'timing': lambda i: i['families'][0]['members'][0].__setitem__(5, 1),
            'grouping': lambda i: self.fam_in(i, 'dir:Solidity/Yul/').update(family='dir:X/'),
            'orphan list': lambda i: i['certified_orphan_families'].append('dir:Solidity/Source/'),
            'consumer kind': lambda i: i['roots']['consumers'][0].update(kind='blanket'),
            'gap targets': lambda i: i['gaps'][0].update(targets=0),
            'closed set': lambda i: i['sets']['S_demand'].update(size=1),
            'counts': lambda i: self.fam_in(i, 'dir:Solidity/Yul/')['counts'].update(keep=0),
            'revision': lambda i: i.update(revision='0' * 40),
            'provenance': lambda i: i['timing']['provenance'].update(command=''),
        }
        for name, edit in cases.items():
            with self.subTest(name):
                self.assertNotEqual(self.tampered(edit), [], name)

    @staticmethod
    def fam_in(inv, name):
        return next(f for f in inv['families'] if f['family'] == name)

    def test_stale_or_altered_extraction_is_rejected(self):
        cdir = Path(self.tmp) / INV.CACHE_ROOT / self.rev
        log = cdir / 'build.log'
        saved = log.read_text()
        try:
            log.write_text(saved + 'x')
            with self.assertRaises(SystemExit):
                INV.Inputs(self.tmp, self.rev)
            self.assertNotEqual(CH.check(Path(self.tmp), self.inv), [])
        finally:
            log.write_text(saved)
        ident = json.loads((cdir / 'identity.json').read_text())
        bad = dict(ident, lean_tree_id='0' * 64)
        (cdir / 'identity.json').write_text(json.dumps(bad))
        try:
            with self.assertRaises(SystemExit):
                INV.Inputs(self.tmp, self.rev)
        finally:
            (cdir / 'identity.json').write_text(json.dumps(ident))

    def test_check_mode_detects_drift_and_does_not_rewrite(self):
        self.out.write_text(self.text.replace('"orphan"', '"keep"', 1))
        before = self.out.read_text()
        code = INV.main(['--repo', self.tmp, '--revision', self.rev, '--output', str(self.out),
                         '--check'])
        self.assertEqual(code, 1)
        self.assertEqual(self.out.read_text(), before)
        self.out.write_text(self.text)
        self.assertEqual(INV.main(['--repo', self.tmp, '--revision', self.rev, '--output',
                                   str(self.out), '--check']), 0)


if __name__ == '__main__':
    unittest.main()
