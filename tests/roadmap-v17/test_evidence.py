"""Synthetic controls exercise accounting, never certify the real release."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('evidence', ROOT / 'scripts/roadmap-v17-evidence.py')
e = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(e)
REV = '1' * 40


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'gate.log').write_bytes(b'decisive output\n')
        self.gate = {'id': 'a', 'revision': REV, 'command': ['checker', '--strict'],
                     'exit': 0, 'status': 'pass', 'log': 'gate.log',
                     'sha256': e.digest(b'decisive output\n')}
        self.report = {'schema': 1, 'revision': REV, 'gates': [self.gate]}
        self.ledger = {'workPackages': ['G52', 'G54.01', 'S05'],
                       'features': [{'id': 'returnStatement', 'owners': ['G38']}],
                       'combinations': [{'in': ['returnStatement', 'tryStatement']}],
                       'symbolCombinations': [], 'decisions': [{'id': 'D01'}]}
        self.proof = {'name': 'actual.theorem', 'module': 'Solidity.Test', 'revision': REV, 'kind': 'kernel',
                      'axioms': ['propext'], 'premises': [], 'observations': ['exact revert bytes']}
        self.closure = {'imports': ['Solidity.Test'], 'schema': 1, 'revision': REV,
                        'ledgerSha256': e.digest(json.dumps(self.ledger, sort_keys=True).encode()),
                        'theorems': [self.proof], 'claims': [
                            {'id': name, 'revision': REV, 'status': 'done',
                             'theorems': ['actual.theorem'], 'observations': ['exact revert bytes']}
                            for name in e.inventory(self.ledger)]}

    def aggregate(self):
        return e.aggregate(self.report, self.root, REV, ['a'])

    def close(self):
        return e.closure(self.closure, self.ledger, REV, ['Solidity.Test'])

    def test_inhabited_aggregation(self):
        self.assertTrue(self.aggregate()['accountingComplete'])
        self.assertFalse(self.aggregate()['releaseClosed'])

    def test_corruption(self):
        (self.root / 'gate.log').write_text('corruption')
        with self.assertRaisesRegex(ValueError, 'corrupt'): self.aggregate()

    def test_missing_log(self):
        (self.root / 'gate.log').unlink()
        with self.assertRaisesRegex(ValueError, 'missing'): self.aggregate()

    def test_empty_log(self):
        (self.root / 'gate.log').write_bytes(b'')
        self.gate['sha256'] = e.digest(b'')
        with self.assertRaisesRegex(ValueError, 'empty'): self.aggregate()

    def test_failed_gate_not_waived(self):
        self.gate.update(exit=1, status='fail', historical=True)
        self.assertEqual(self.aggregate()['failed'], ['a'])
        self.assertFalse(self.aggregate()['accountingComplete'])

    def test_checkout_changed_during_gate(self):
        self.report['unchangedCheckout'] = False
        with self.assertRaisesRegex(ValueError, 'checkout changed'): self.aggregate()

    def test_pending_gate(self):
        self.gate.update(exit=None, status='pending')
        self.assertFalse(self.aggregate()['accountingComplete'])

    def test_absent_gate(self):
        self.report['gates'] = []
        self.assertEqual(self.aggregate()['missing'], ['a'])

    def test_wrong_revision(self):
        self.gate['revision'] = '2' * 40
        with self.assertRaisesRegex(ValueError, 'revision'): self.aggregate()

    def test_contradictory_exit(self):
        for status, code in [('pass', 1), ('fail', 0), ('pending', 0), ('pass', True)]:
            self.gate.update(status=status, exit=code)
            with self.assertRaises(ValueError): self.aggregate()

    def test_duplicate_gate(self):
        self.report['gates'].append(copy.deepcopy(self.gate))
        with self.assertRaisesRegex(ValueError, 'duplicate'): self.aggregate()

    def test_path_escape_and_symlink(self):
        for path in ['/etc/hosts', '../gate.log']:
            self.gate['log'] = path
            with self.assertRaises(ValueError): self.aggregate()
        (self.root / 'escape').symlink_to('/etc/hosts')
        self.gate['log'] = 'escape'
        with self.assertRaises(ValueError): self.aggregate()

    def test_duplicate_json_key(self):
        (self.root / 'bad.json').write_text('{"revision":1,"revision":2}')
        with self.assertRaisesRegex(ValueError, 'duplicate JSON'): e.load(self.root / 'bad.json')

    def test_inhabited_combination_and_child_accounting(self):
        result = self.close()
        self.assertTrue(result['accountingComplete'])
        self.assertEqual(result['requiredRows'], 6)
        self.assertFalse(result['releaseClosed'])

    def test_missing_child(self):
        self.closure['claims'].pop(0)
        self.assertFalse(self.close()['accountingComplete'])

    def test_incomplete_prerequisite(self):
        self.closure['claims'][0]['status'] = 'blocked'
        self.assertFalse(self.close()['accountingComplete'])

    def test_wrong_ledger_and_changed_profile(self):
        self.ledger['features'][0]['owners'] = ['G47']
        with self.assertRaisesRegex(ValueError, 'ledger'): self.close()

    def test_parameterized_only(self):
        self.proof['kind'] = 'parameterized'
        with self.assertRaisesRegex(ValueError, 'parameterized'): self.close()

    def test_external_test_is_not_kernel(self):
        self.proof['kind'] = 'external-test'
        with self.assertRaises(ValueError): self.close()

    def test_missing_premise(self):
        self.proof['premises'] = ['not.integrated']
        with self.assertRaisesRegex(ValueError, 'premise'): self.close()

    def test_cycle(self):
        self.proof['premises'] = ['actual.theorem']
        with self.assertRaisesRegex(ValueError, 'undischarged'): self.close()

    def test_explicit_acyclic_discharge(self):
        self.closure['theorems'].append(dict(self.proof, name='leaf', premises=[]))
        self.proof['premises'] = ['leaf']
        self.assertTrue(self.close()['accountingComplete'])

    def test_unapproved_axiom(self):
        self.proof['axioms'].append('sorryAx')
        with self.assertRaisesRegex(ValueError, 'axiom'): self.close()

    def test_unmatched_observation(self):
        self.closure['claims'][0]['observations'].append('callback rollback')
        with self.assertRaisesRegex(ValueError, 'observation'): self.close()

    def test_duplicate_and_unknown_claim(self):
        self.closure['claims'].append(copy.deepcopy(self.closure['claims'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate'): self.close()
        self.closure['claims'][-1]['id'] = 'child:G99'
        with self.assertRaisesRegex(ValueError, 'unknown'): self.close()

    def test_wrong_theorem_revision(self):
        self.proof['revision'] = '2' * 40
        with self.assertRaisesRegex(ValueError, 'revision'): self.close()

    def test_unclosed_extra_theorem(self):
        self.closure['theorems'].append(dict(self.proof, name='unclosed', kind='parameterized'))
        self.assertFalse(self.close()['accountingComplete'])

    def test_missing_public_import(self):
        self.closure['imports'] = []
        with self.assertRaisesRegex(ValueError, 'import'): self.close()

    def test_unimported_theorem(self):
        self.proof['module'] = 'Solidity.Unpublished'
        with self.assertRaisesRegex(ValueError, 'public imports'): self.close()

    def test_mislabeled_gate_command(self):
        self.gate['id'] = 'runtime-keysort'
        self.gate['command'] = ['true']
        with self.assertRaisesRegex(ValueError, 'mislabeled'):
            e.aggregate(self.report, self.root, REV, ['runtime-keysort'])

    def test_snapshot_mismatch(self):
        current = {'revision': REV, 'inputs': {'pin': 'hash'}, 'runtime': {'lean': 'binary'}}
        self.assertTrue(e.verify_snapshot(copy.deepcopy(current), current)['accountingComplete'])
        changed = copy.deepcopy(current)
        changed['runtime']['lean'] = 'different'
        with self.assertRaisesRegex(ValueError, 'snapshot'): e.verify_snapshot(changed, current)

    def test_real_ledger_inventory(self):
        ledger = e.load(ROOT / e.LEDGER)
        rows = e.inventory(ledger)
        self.assertEqual(len(rows), 457)
        self.assertIn('child:G54.03', rows)
        self.assertIn('feature:fixedPoint', rows)

    def generated_fixture(self):
        report = e.load(ROOT / 'tests/generated/seed-0.json')
        report['metadata']['checkoutCommit'] = REV
        paths = {'runnerSha256': 'scripts/evm-reference/generated.mjs',
                 'replaySha256': 'scripts/evm-reference/replay.mjs',
                 'lockSha256': 'scripts/evm-reference/package-lock.json',
                 'driverSha256': 'SolCases.lean', 'generatorSha256': 'Solidity/Tools/SolCases.lean',
                 'generatorBinarySha256': '.lake/build/bin/solcases'}
        for field, path in paths.items():
            dest = self.root / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(b'synthetic provenance control')
            report['metadata'][field] = e.digest(dest.read_bytes())
        dest = self.root / 'scripts/solidity-upstream.mjs'
        dest.write_text("export const COMPILER_SHA = '" + report['metadata']['compilerSha256'] + "'")
        return report

    def test_complete_synthetic_matrix(self):
        report = self.generated_fixture()
        # Mock only execution of reserved producer; this is a structural unit control.
        with patch.object(e, 'published_differential') as producer:
            self.assertTrue(e.differential(report, self.root, REV)['accountingComplete'])
            producer.assert_called_once()

    def test_missing_kind_and_variant_and_summary(self):
        for mutation in ('kind', 'variant', 'summary', 'source', 'observation', 'stale'):
            report = self.generated_fixture()
            if mutation == 'kind':
                for row in report['records']: row['record']['kind'] = 0
            elif mutation == 'variant': report['records'][0]['variants'].pop()
            elif mutation == 'summary': report['summary']['agree'] = 641
            elif mutation == 'source': report['records'][0]['record']['source'] += 'changed'
            elif mutation == 'observation': report['records'][0]['variants'][0]['run'] = None
            else: report['metadata']['runnerSha256'] = '0' * 64
            with patch.object(e, 'published_differential'):
                with self.assertRaises(ValueError, msg=mutation): e.differential(report, self.root, REV)

    def compare(self, report):
        return subprocess.run(['node', str(ROOT / 'scripts/roadmap-v17-compare.mjs')],
                              input=json.dumps(report).encode(), capture_output=True, timeout=60)

    def test_published_comparator_retention_controls(self):
        # Actual historical external observations, never relabeled same-revision evidence.
        original = e.load(ROOT / 'tests/generated/seed-0.json')
        passed = self.compare(original)
        self.assertEqual(passed.returncode, 0, passed.stderr.decode())
        for mutation in ('bytes', 'rollback', 'initial', 'settings', 'null', 'layout', 'values', 'exception', 'metrics'):
            report = copy.deepcopy(original)
            actual = report['records'][0]['variants'][0]
            if mutation == 'bytes': actual['run']['returnData'] = '0x1234'
            elif mutation == 'rollback': actual['rawStorage'] = ['99', '99']
            elif mutation == 'initial': actual['before']['returnData'] = '0x'
            elif mutation == 'settings': actual['inputSha256'] = '0' * 64
            elif mutation == 'layout': actual['layout'] = {}
            elif mutation == 'values': actual['run']['values'] = ['999']
            elif mutation == 'metrics': actual['run'].pop('steps')
            elif mutation == 'exception': actual['run']['exception'] = 'unexpected'
            else: actual['run'] = None
            self.assertNotEqual(self.compare(report).returncode, 0, mutation)

    def test_historical_generated_report_refused(self):
        report = e.load(ROOT / 'tests/generated/seed-0.json')
        with self.assertRaisesRegex(ValueError, 'historical'): e.differential(report, ROOT, REV)


if __name__ == '__main__':
    unittest.main()
