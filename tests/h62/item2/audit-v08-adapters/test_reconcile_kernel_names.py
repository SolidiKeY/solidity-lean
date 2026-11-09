"""Guard lost, ambiguous and forged name-accounting metadata; no Lean proofs."""
import hashlib
import importlib.util
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT / 'scripts/h62/item2/audit-v08-adapters'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('kernel_names', SCRIPTS / 'reconcile_kernel_names.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def lexical(name, ident=None):
    return {'id': ident or name, 'file': 'A.lean', 'name_candidate': name, 'signature_source': None}


def kernel(name, module='A'):
    expr = 'synthetic metadata, not a kernel proof'
    return {'name': name, 'module': module, 'type_expr': expr,
            'type_sha256': hashlib.sha256(expr.encode()).hexdigest()}


class Names(unittest.TestCase):
    def reconcile(self, source, rows):
        return m.reconcile({'declarations': source}, {'declarations': rows}, modules=('A',))

    def test_public_private_and_kernel_only_all_retained(self):
        owned = {**lexical('A.public'), 'owner_status': 'HISTORICAL_HINT',
                 'owner_relay': {'owner': 'unconfirmed snapshot owner'}}
        result = self.reconcile([owned, lexical('A.private')],
                                [kernel('A.public'), kernel('_private.A.7.A.private'), kernel('A.generated')])
        self.assertEqual([r['name_status'] for r in result['lexical']],
                         ['PUBLIC_NAME_CANDIDATE', 'PRIVATE_NAME_CANDIDATE'])
        self.assertEqual(result['kernel_only_pending'], ['A.generated'])
        self.assertEqual(len(result['kernel']), 3)
        self.assertEqual(result['lexical'][0]['snapshot_owner_relay'], owned['owner_relay'])
        self.assertEqual(result['lexical'][0]['owner_status'], 'UNCONFIRMED')
        self.assertEqual(result['new_witnesses'], 0)
        self.assertEqual(result['statement_fidelity_verified'], 0)
        self.assertTrue(all(r['statement_fidelity'] == 'PENDING' for r in result['lexical']))

    def test_ambiguity_is_not_resolved_by_first_match(self):
        result = self.reconcile([lexical('A.same')],
                                [kernel('_private.A.0.A.same'), kernel('_private.A.1.A.same')])
        self.assertEqual(result['lexical'][0]['name_status'], 'AMBIGUOUS_NAME')
        self.assertEqual(len(result['lexical'][0]['kernel_candidates']), 2)
        self.assertTrue(all(r['lexical_ids'] == ['A.same'] for r in result['kernel']))

    def test_missing_and_unknown_private_spellings_stay_pending(self):
        for spelling in ('_private.foreign.0.A.missing',
                         '_private.A.not_a_counter.A.missing', '_private.A.٠.A.missing'):
            result = self.reconcile([lexical('A.missing')], [kernel(spelling)])
            self.assertEqual(result['lexical'][0]['name_status'], 'NO_NAME_MATCH')
            self.assertEqual(result['kernel_only_pending'], [spelling])
            self.assertEqual(result['kernel'][0]['normalized_name_candidate'], None)

    def test_duplicate_scope_and_digest_refusals(self):
        source, rows = [lexical('A.x')], [kernel('A.x')]
        for changed_source, changed_rows in [
                (source * 2, rows), (source, rows * 2), (source, []),
                (source, [kernel('A.x', module='B')]),
                (source, [{**rows[0], 'type_sha256': 'wrong'}])]:
            with self.assertRaises(ValueError):
                self.reconcile(changed_source, changed_rows)

    def test_outside_scope_is_counted_not_claimed(self):
        outside = {**lexical('B.x'), 'file': 'B.lean'}
        result = self.reconcile([lexical('A.x'), outside], [kernel('A.x')])
        self.assertEqual(result['lexical_scope_total'], 1)
        self.assertEqual(result['lexical_outside_scope'], 1)
        self.assertEqual(result['lexical_input_total'], 2)
        self.assertFalse(result['complete_interface_inventory'])


if __name__ == '__main__':
    unittest.main()
