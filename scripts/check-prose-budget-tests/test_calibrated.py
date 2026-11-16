"""Inactive candidate controls; published fixtures remain separate from current bounds."""
import copy
from fractions import Fraction
import importlib.machinery
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'check-prose-budget'
loader = importlib.machinery.SourceFileLoader('calibrated_checker', str(SCRIPT))
spec = importlib.util.spec_from_loader(loader.name, loader)
check = importlib.util.module_from_spec(spec)
loader.exec_module(check)


class Calibrated(unittest.TestCase):
    def test_current_policy_within_published_bounds(self):
        baseline = check.read_baseline(SCRIPT.with_name('prose-baseline.json'))
        check.validate_candidate(baseline['_candidate'])

    def test_published_fixture(self):
        original = check.published_candidate()
        entry = original['calibration']['Solidity/Automation']['metrics']['comment_lines']
        self.assertEqual(Fraction(entry['ratio']), Fraction(14, 19))
        self.assertEqual(Fraction(entry['margin']), 0)
        self.assertFalse(original['active'])
        self.assertIsNone(original['goal_decl'])

    def test_shrink_and_equivalent_rationals(self):
        policy = check.published_candidate()
        entry = policy['calibration']['Solidity/Backend']['metrics']['comment_lines']
        for key in ('ratio', 'margin'):
            value = Fraction(entry[key])
            entry[key] = f'{value.numerator * 2}/{value.denominator * 2}'
        check.validate_candidate(policy)
        entry['ratio'] = '0'
        entry['margin'] = '0'
        check.validate_candidate(policy)
        # A second update must also be monotone against its prior version.
        raised = copy.deepcopy(policy)
        raised['calibration']['Solidity/Backend']['metrics']['comment_lines']['ratio'] = '1/999999'
        with self.assertRaises(ValueError):
            check.validate_candidate(raised, ceiling=policy)

    def test_frozen_fields_and_increases(self):
        original = check.published_candidate()
        variants = []
        for key, value in [('active', True), ('goal_decl', 'closed'), ('excluded_until_r1', []), ('version', 'new')]:
            p = copy.deepcopy(original)
            p[key] = value
            variants.append(p)
        p = copy.deepcopy(original)
        p['calibration'].pop('Solidity/Automation')
        variants.append(p)
        for key, value in [('ratio', '1000000'), ('margin', '-1'), ('ratio', '1/0')]:
            p = copy.deepcopy(original)
            p['calibration']['Solidity/Automation']['metrics']['comment_lines'][key] = value
            variants.append(p)
        p = copy.deepcopy(original)
        p['calibration']['Solidity/Automation']['denominator_source'] = 'repository-solidity'
        variants.append(p)
        for p in variants:
            with self.assertRaises(ValueError):
                check.validate_candidate(p)

    def test_physical_denominator(self):
        for source, expected in [('', 0), ('-- comment\n', 0), ('/- nested /- x -/ -/\n', 0),
                                 ('def x := 1 -- mixed\n', 1), ('\n \n', 0),
                                 ('def x := "-- literal"\n', 1), ('/- x -/ def x := 1', 1),
                                 ('-- generated\ndef x := 1\n', 1)]:
            self.assertEqual(check.code_lines(source), expected)

    def test_diagnostic_legacy_failure_and_audits(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Solidity').mkdir()
            (root / 'docs/audits').mkdir(parents=True)
            (root / 'Solidity/New.lean').write_text('-- new\ndef x := 1\n')
            (root / 'docs/audits/new.md').write_text('audit\n')
            policy = check.published_candidate()
            actual = check.counts(root)
            report = check.candidate_report(root, actual, policy)
            row = next(r for r in report['rows'] if r['area'] == 'Solidity/_root' and r['metric'] == 'comment_lines')
            self.assertEqual(row['denominator'], 1)
            audit = next(r for r in report['rows'] if r['area'] == 'docs/audits' and r['metric'] == 'docs_lines')
            self.assertEqual(audit['numerator'], 1)
            self.assertFalse(audit['enforced'])
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps({'_candidate': policy}))
            before = baseline.read_bytes()
            for flags in ([], ['--candidate', check.CANDIDATE_VERSION], ['--candidate', check.CANDIDATE_VERSION, '--update']):
                run = subprocess.run([sys.executable, str(SCRIPT), '--root', str(root), '--baseline', str(baseline), *flags], capture_output=True, text=True)
                self.assertEqual(run.returncode, 1, run.stderr)
                self.assertIn('Prose budget exceeded', run.stderr)
                self.assertEqual(baseline.read_bytes(), before)

    def test_zero_denominator_unseen_and_update(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Solidity').mkdir()
            (root / 'docs').mkdir()
            policy = check.published_candidate()
            report = check.candidate_report(root, {'Solidity/Unseen': dict.fromkeys(check.METRICS, 1)}, policy)
            unseen = [r for r in report['rows'] if r['area'] == 'Solidity/Unseen']
            self.assertTrue(all(r['denominator'] == 0 and r['allowance'] == '0' and not r['passed'] for r in unseen))
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps({'_candidate': policy}))
            run = subprocess.run([sys.executable, str(SCRIPT), '--root', str(root), '--baseline', str(baseline), '--update'], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(json.loads(baseline.read_text())['_candidate'], policy)


    def test_candidate_import_is_monotone_and_preserves_legacy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Solidity').mkdir()
            (root / 'docs').mkdir()
            policy = check.published_candidate()
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps({'_candidate': policy}))
            proposed = root / 'proposed.json'
            cell = policy['calibration']['Solidity/Backend']['metrics']['comment_lines']
            cell['ratio'] = '0'
            cell['margin'] = '0'
            proposed.write_text(json.dumps(policy))
            command = [sys.executable, str(SCRIPT), '--root', str(root), '--baseline', str(baseline), '--update', '--candidate-update', str(proposed)]
            run = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(json.loads(baseline.read_text())['_candidate'], policy)
            before = baseline.read_bytes()
            cell['ratio'] = '1/999999'
            proposed.write_text(json.dumps(policy))
            run = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(run.returncode, 2, run.stderr)
            self.assertEqual(baseline.read_bytes(), before)

    def test_mapping_generated_claims_and_rational_boundary(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Solidity/Automation').mkdir(parents=True)
            (root / 'Solidity/Other').mkdir()
            (root / 'docs/audits').mkdir(parents=True)
            (root / 'Solidity/Automation/A.lean').write_text('-- generated H123\ndef x := 1 -- comment\n')
            (root / 'Solidity/Other/B.lean').write_text('def y := 2\ndef z := 3\n')
            (root / 'docs/audits/a.md').write_text('generated\n')
            actual = check.counts(root)
            policy = check.published_candidate()
            entry = policy['calibration']['Solidity/Automation']['metrics']['comment_lines']
            entry['ratio'] = '1/2'
            entry['margin'] = '0'
            # Two comments over one own code line fail; other-area growth cannot help.
            report = check.candidate_report(root, actual, policy)
            row = next(r for r in report['rows'] if r['area'] == 'Solidity/Automation' and r['metric'] == 'comment_lines')
            self.assertEqual((row['numerator'], row['denominator'], row['allowance'], row['passed']), (2, 1, '1/2', False))
            audit = next(r for r in report['rows'] if r['area'] == 'docs/audits' and r['metric'] == 'docs_lines')
            self.assertEqual(audit['denominator'], 3)
            self.assertFalse(audit['enforced'])
            # Exercise equality and a one-unit excess without rounding.
            actual['Solidity/Automation']['comment_lines'] = 0
            row = next(r for r in check.candidate_report(root, actual, policy)['rows'] if r['area'] == 'Solidity/Automation' and r['metric'] == 'comment_lines')
            self.assertTrue(row['passed'])
            self.assertEqual(actual['Solidity/Automation']['process_ids'], 1)
