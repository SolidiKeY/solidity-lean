"""Guard the hidden-return-input regression without asserting feasibility.
Existential outputs, nested binder arrows and iff results are not hypotheses.
"""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'scripts/h62/item2/audit-v09-passes'))
import premises


class ReturnInputAcceptance(unittest.TestCase):
    def test_forall_arrow_chain_and_exact_spans(self):
        text = '∀ (f : Nat → Nat), ∀ x, f x = x → Good f x'
        result = premises.return_inputs(text)
        self.assertEqual([r['source'] for r in result['inputs']],
                         ['∀ (f : Nat → Nat),', '∀ x,', 'f x = x'])
        self.assertEqual(result['remainder'], 'Good f x')
        for row in result['inputs']:
            a, b = row['span']; self.assertEqual(text[a:b], row['source'])
        self.assertIsNone(result['simultaneous_witness'])
        self.assertEqual(result['implicit_inclusion'], 'pending Lean')

    def test_data_domain_is_not_claimed_a_proof(self):
        row, = premises.return_inputs('Nat → Fin W')['inputs']
        self.assertEqual(row['kind'], 'arrow-domain; Prop-or-data-pending')

    def test_existential_and_let_barriers(self):
        for text in ['∃ x, P x → Q x', 'let x := a; P x → Q x', 'type_of% (f x)']:
            self.assertEqual(premises.return_inputs(text)['inputs'], [])

    def test_nested_quantifier_and_iff_are_not_outer_arrows(self):
        for text in ['P ∧ ∀ x, Q x → R x', 'P → Q ↔ R', 'P ↔ Q → R']:
            self.assertEqual(premises.return_inputs(text)['inputs'], [])

    def test_parenthesized_domain_and_result(self):
        result = premises.return_inputs('( (∀ x, P x) → Q )')
        self.assertEqual([r['source'] for r in result['inputs']], ['(∀ x, P x)'])
        self.assertEqual(result['remainder'], 'Q')

    def test_ascii_forall_and_arrow(self):
        result = premises.return_inputs('forall x, P x -> Q x')
        self.assertEqual([r['source'] for r in result['inputs']], ['forall x,', 'P x'])

    def test_comments_do_not_add_inputs(self):
        self.assertEqual(premises.return_inputs('P /- → False -/')['inputs'], [])


if __name__ == '__main__': unittest.main()
