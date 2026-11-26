import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "check-prose-budget"
MODULE = runpy.run_path(str(SCRIPT))

# Independent inventory of pinned Init/Lean/Lake interpolatedStr declarations.
BUILTIN_CASES = {
    's!': 's! ', 'm!': 'm! ', 'f!': 'f! ', 'v!': 'v!',
    'dbg_trace': 'dbg_trace ', 'println!': 'println! ',
    'throwError': 'throwError ', 'reportIssue!': 'reportIssue! ',
    'throwErrorAt': 'throwErrorAt stx ',
    'throwNamedError': 'throwNamedError sample.error. ',
    'logNamedError': 'logNamedError sample.error. ',
    'logNamedWarning': 'logNamedWarning sample.error. ',
    'throwNamedErrorAt': 'throwNamedErrorAt stx sample.error. ',
    'logNamedErrorAt': 'logNamedErrorAt stx sample.error. ',
    'logNamedWarningAt': 'logNamedWarningAt stx sample.error. ',
    'trace[': 'trace[category] ', 'trace_goal[': 'trace_goal[category] ',
    'Macro.trace[': 'Macro.trace[category] ',
}


REFERENCE_CASES = (
    '.missing', '.(stx)', '‹Syntax›', '‹Lean.Syntax›', '⟨stx⟩',
    '#[]', '#[stx]', '#v[stx]', '%[stx|xs]', '·', '⋯',
    '↑stx', '⇑stx', '↥stx', 'no_index stx', 'no_index(stx)',
    'private_decl% stx', 'type_of% stx', 'no_implicit_lambda% stx',
    'no_implicit_lambda%stx', 'value_of% stx',
    'ensure_expected_type% "ordinary /-- text -/" stx',
    'unop% id stx', 'binop% f stx stx', 'binop_lazy% f stx stx',
    'binrel% f stx stx', 'binrel_no_prop% f stx stx',
    'leftact% f stx stx', 'rightact% f stx stx',
    'for_in% x y z', "for_in'% x y z", 'decl_name%',
    'default_or_ofNonempty%', 'default_or_ofNonempty% unsafe',
    'default_or_ofNonempty%unsafe', 'exact?%', '_', '?m',
    '1E10', '1E-3', '1.2E+3', '1.2E-3', '1#w', '1#(width)',
    '1#↑w', '1#(8+1)', '1#no_index w', "1#'w", "x#'w",
    "(f x)#'w", '1...*', '*...*', '1<...*', '1 ...*', '1 <...*',
    '1 /- gap -/ <...*',
    '1.2e-3', '1.2e+3', '1e-3', '1#8', '0xF', '0b10', '0o7',
)


class ScannerTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        source = '\n'.join([
            'def x := "-- /- fake -/"',
            'def y := r##"/- " -- fake"##',
            "def c := '\"'",
            'def «/- hidden -/» := 1',
            '/- outer',
            '  /- nested -/',
            '',
            'end -/ -- same line',
            '-- tail',
        ])
        self.assertEqual(MODULE['comment_lines'](source), (5, 0))

    def test_interpolation(self):
        for prefix in ('s', 'm', 'f'):
            self.assertEqual(MODULE['comment_lines'](prefix + '!"{"--"}"'), (0, 0))
            self.assertEqual(MODULE['comment_lines'](prefix + '!"{ /- real -/ 1 }"'), (1, 0))
        self.assertEqual(MODULE['comment_lines']('def x := s!"{ /- real -/ 1 }"'), (1, 0))
        self.assertEqual(MODULE['comment_lines']('s!"{s!"{ /-- nested -/ 1 }"}"'), (1, 1))
        self.assertEqual(MODULE['comment_lines'](r's!"\{ /- literal -/ }"'), (0, 0))

    def test_interpolation_trivia(self):
        for prefix in ('s', 'm', 'f'):
            for trivia, count in [('', 1), (' ', 1), ('\t', 1), ('\n', 1),
                                  ('\r\n', 1), ('/- gap -/', 1),
                                  ('/- outer /- inner -/ -/ ', 1),
                                  ('-- gap\n', 2), ('/- gap\n\n-/ ', 3),
                                  ('/- gap -/-- gap\n ', 2)]:
                with self.subTest(prefix=prefix, trivia=trivia):
                    source = 'def x := ' + prefix + '!' + trivia + '"{ /-- real -/ 1 }"'
                    self.assertEqual(MODULE['comment_lines'](source), (count, 1))
            self.assertEqual(MODULE['comment_lines'](prefix + '! "{"--"}"'), (0, 0))
            self.assertEqual(MODULE['comment_lines'](prefix + r'! "\{ /-- literal -/ }"'), (0, 0))

    def test_nested_interpolated_terms(self):
        self.assertEqual(MODULE['comment_lines']('s! "{{ /-- real -/ x := 1 : S }}"'), (1, 1))
        self.assertEqual(MODULE['comment_lines']('s! "{m! /- gap -/ "{ /-- real -/ 1 }"}"'), (1, 1))

    def test_interpolation_keyword_boundaries(self):
        for name in ('names!', 'Names.s!', '℘s!', 's!suffix', 's!.field'):
            with self.subTest(name=name):
                self.assertEqual(MODULE['comment_lines'](name + ' "{ /-- literal -/ 1 }"'), (0, 0))

    def test_literal_prefix_boundaries(self):
        for identifier in ("x'", "x₁'", "℘'", "Ns.x'"):
            with self.subTest(identifier=identifier):
                source = "#check f " + identifier + "\x20'\"' -- real"
                self.assertEqual(MODULE['comment_lines'](source), (1, 0))
        for name in ('bar', 'Ns.r'):
            with self.subTest(name=name):
                source = name + r'"escaped \" /- literal -/"'
                self.assertEqual(MODULE['comment_lines'](source), (0, 0))

    def test_all_builtin_interpolation_forms(self):
        self.assertEqual(set(MODULE['_INTERPOLATORS']), set(BUILTIN_CASES))
        for name, introducer in BUILTIN_CASES.items():
            with self.subTest(name=name):
                source = introducer + '"{ /-- first\nsecond\n-/ 1 }"'
                self.assertEqual(MODULE['comment_lines'](source), (3, 3))

    def test_debug_trace_trivia(self):
        for trivia, expected in [(' ', (3, 3)), ('\n', (3, 3)),
                                 ('/- gap -/ ', (3, 3)), ('-- gap\n', (4, 3))]:
            with self.subTest(trivia=trivia):
                self.assertEqual(MODULE['comment_lines']('dbg_trace' + trivia +
                                 '"{ /-- first\nsecond\n-/ 1 }"'), expected)

    def test_diagnostic_reference_arguments(self):
        for name in ('throwErrorAt', 'throwNamedErrorAt', 'logNamedErrorAt', 'logNamedWarningAt'):
            label = ' sample.error.' if name != 'throwErrorAt' else ''
            source = name + ' (mkRef "{ /-- literal -/ 0 }")' + label + '\n"{ /-- real -/ 1 }"'
            with self.subTest(name=name):
                self.assertEqual(MODULE['comment_lines'](source), (1, 1))
        for reference in ('(stx[0][1]).raw', '(stx[0]!)', "(stx[0]'h)", 'ref.{0}',
                          '`throwErrorAt', '(stx).raw', '`(term| "{ /-- literal -/ }")'):
            with self.subTest(reference=reference):
                source = 'throwErrorAt ' + reference + '\n"{ /-- real -/ 1 }"'
                self.assertEqual(MODULE['comment_lines'](source), (1, 1))
        self.assertEqual(MODULE['comment_lines'](
            'throwErrorAt (/- gap -/ stx).raw\n"{ /-- real -/ 1 }"'), (2, 1))

    def test_comments_between_diagnostic_arguments(self):
        source = ('throwNamedErrorAt -- prefix\n(stx) -- reference\n'
                  'sample.error. -- name\n"{ /-- real -/ 1 }"')
        self.assertEqual(MODULE['comment_lines'](source), (4, 1))
        source = 'trace[-- category\nfoo.«a]b»-- end\n]\n"{ /-- real -/ 1 }"'
        self.assertEqual(MODULE['comment_lines'](source), (3, 1))

    def test_deep_reference_groups(self):
        source = 'throwErrorAt ' + '(' * 2000 + 'stx' + ')' * 2000 + ' "{ /-- real -/ 1 }"'
        self.assertEqual(MODULE['comment_lines'](source), (1, 1))

    def test_maximal_reference_atoms(self):
        for reference in REFERENCE_CASES:
            for introducer in ('throwErrorAt ', 'throwNamedErrorAt '):
                label = ' sample.error.' if 'Named' in introducer else ''
                with self.subTest(reference=reference, introducer=introducer):
                    source = introducer + reference + label + '\n"{ /-- first\nsecond\n-/ 1 }"'
                    self.assertEqual(MODULE['comment_lines'](source),
                                     (4 if '/- gap -/' in reference else 3, 3))

    def test_reference_precedence(self):
        for reference in ('Type 0', 'Sort 0'):
            self.assertEqual(MODULE['comment_lines']('throwErrorAt ' + reference +
                             ' "{ /-- literal -/ 1 }"'), (0, 0))

    def test_trace_categories_and_quoted_names(self):
        for intro in ('trace[foo.«bar]baz»]', 'Macro.trace[«a]b»]', 'trace_goal[foo.bar]'):
            with self.subTest(intro=intro):
                self.assertEqual(MODULE['comment_lines'](intro + '\n"{ /-- real -/ 1 }"'), (1, 1))
        for name in ('`dbg_trace', '``s!', '`throwErrorAt', '«dbg_trace»',
                     'Ns.«s!»', 'Ns.dbg_trace', 'dbg_traceExtra', 'versions!'):
            with self.subTest(name=name):
                self.assertEqual(MODULE['comment_lines'](name + ' "{ /-- literal -/ 1 }"'), (0, 0))

    def test_noninterpolated_message_terms(self):
        for intro in ('dbg_trace', 'println!', 'throwError', 'throwErrorAt stx',
                      'throwNamedError sample.error.', 'trace[category]'):
            with self.subTest(intro=intro):
                self.assertEqual(MODULE['comment_lines'](intro + ' ("{ /-- literal -/ 1 }")'), (0, 0))
        # Lake's v! declaration alone uses noWs.
        self.assertEqual(MODULE['comment_lines']('v! "{ /-- literal -/ 1 }"'), (0, 0))

    def test_docstrings(self):
        self.assertEqual(MODULE['comment_lines']('/-- docs\n/- nested -/\n-/\n/-! module -/'), (4, 4))
        self.assertEqual(MODULE['comment_lines']('/- plain /-- doc -/ end -/'), (1, 1))
        self.assertEqual(MODULE['comment_lines']('"escaped \\\" /- fake -/" -- real'), (1, 0))
        self.assertEqual(MODULE['comment_lines']('-- no final newline'), (1, 0))


class AcceptanceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'Solidity/Automation').mkdir(parents=True)
        (self.root / 'docs').mkdir()
        self.lean = self.root / 'Solidity/Automation/A.lean'
        self.baseline = self.root / 'baseline.json'
        self.policy = MODULE['activation_policy']()
        self.baseline.write_text(json.dumps({'_candidate': self.policy}))

    def run_script(self, *args):
        return subprocess.run([sys.executable, '-B', str(SCRIPT), '--root', str(self.root),
                               '--baseline', str(self.baseline), *args], capture_output=True, text=True)

    def source(self, code, comments):
        self.lean.write_text('def x := 1\n' * code + '-- comment\n' * comments)

    def test_growth_with_code_at_frozen_ratio(self):
        self.source(19, 14)
        self.assertEqual(self.run_script().returncode, 0)
        self.source(38, 28)
        self.assertEqual(self.run_script().returncode, 0)

    def test_prose_only_growth_fails_without_partial_write(self):
        self.source(19, 15)
        before = self.baseline.read_bytes()
        for flags in ((), ('--update',), ('--candidate', MODULE['CANDIDATE_VERSION'])):
            run = self.run_script(*flags)
            self.assertEqual(run.returncode, 1, run.stderr)
            self.assertIn('Prose budget exceeded', run.stderr)
            self.assertEqual(self.baseline.read_bytes(), before)

    def test_scanned_interpolation_growth(self):
        for introducer in BUILTIN_CASES.values():
            with self.subTest(introducer=introducer):
                self.lean.write_text('def x := 1\n' * 18 + introducer + '"{1}"\n' + '-- comment\n' * 14)
                self.assertEqual(self.run_script().returncode, 0)
                self.lean.write_text(self.lean.read_text().replace('{1}', '{ /-- new\nsecond\n-/ 1 }'))
                self.assertEqual(self.run_script('--update').returncode, 1)

    def test_unseen_area_allows_nothing(self):
        self.source(100, 0)
        (self.root / 'Solidity/Unseen').mkdir()
        (self.root / 'Solidity/Unseen/A.lean').write_text('-- prose\ndef x := 1\n' * 100)
        self.assertEqual(self.run_script('--update').returncode, 1)

    def test_residual_shrink_and_no_regrowth(self):
        original = MODULE['activation_policy']()
        smaller = MODULE['activation_policy']()
        area = next(iter(smaller['activation']['residuals']))
        metric = next(iter(smaller['activation']['residuals'][area]))
        smaller['activation']['residuals'][area][metric] = '0'
        MODULE['validate_active'](smaller, original)
        with self.assertRaisesRegex(ValueError, 'residual increase'):
            MODULE['validate_active'](original, smaller)
        proposed = self.root / 'proposed.json'
        proposed.write_text(json.dumps(smaller))
        self.source(19, 14)
        self.assertEqual(self.run_script('--update', '--candidate-update', str(proposed)).returncode, 0)
        proposed.write_text(json.dumps(original))
        before = self.baseline.read_bytes()
        self.assertEqual(self.run_script('--update', '--candidate-update', str(proposed)).returncode, 2)
        self.assertEqual(self.baseline.read_bytes(), before)

    def test_update_does_not_train_ratios(self):
        self.source(19, 0)
        self.assertEqual(self.run_script('--update').returncode, 0)
        updated = json.loads(self.baseline.read_text())['_candidate']
        self.assertEqual(updated['calibration'], self.policy['calibration'])
        self.assertTrue(all(value == '0' for row in updated['activation']['residuals'].values() for value in row.values()))

    def test_frozen_active_fields(self):
        import copy
        for field, value in [('active', False), ('excluded_until_r1', []), ('activation', {})]:
            p = copy.deepcopy(self.policy)
            p[field] = value
            with self.assertRaises(ValueError):
                MODULE['validate_active'](p)
        for field in ('ratio', 'margin'):
            p = copy.deepcopy(self.policy)
            p['calibration']['Solidity/Automation']['metrics']['comment_lines'][field] = '0'
            with self.assertRaises(ValueError):
                MODULE['validate_active'](p)

    def test_missing_source_and_bad_baseline(self):
        (self.root / 'docs').rmdir()
        self.assertEqual(self.run_script('--update').returncode, 2)
        self.baseline.write_text('{"legacy": {}}')
        self.assertEqual(self.run_script().returncode, 2)


if __name__ == '__main__':
    unittest.main()
