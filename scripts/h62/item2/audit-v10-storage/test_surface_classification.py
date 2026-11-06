#!/usr/bin/env python3
"""Boundary regressions for static extraction; no Lean claims."""
import unittest
from surface_classification import classify

class SurfaceTests(unittest.TestCase):
    def test_dependent_group_and_nested_colons(self):
        s='theorem f {E : Env} (locals : Locals E.layout []) (h : (fun x : Nat => x) 0 = 0) : True'
        f=classify(s)
        self.assertEqual([b['names'] for b in f['declaration_binders']], [['E'],['locals'],['h']])
        self.assertEqual(f['declaration_binders'][1]['type_source'], 'Locals E.layout []')

    def test_leading_forall_preserves_joint_inputs(self):
        s='theorem f : ∀ (E : Env) (h : E.ok = true), P E h'
        f=classify(s)
        self.assertEqual(f['leading_forall_source'], ' (E : Env) (h : E.ok = true)')
        self.assertEqual(f['result_source'], ' ∀ (E : Env) (h : E.ok = true), P E h')

    def test_arrows_not_promoted_to_prop_hypotheses(self):
        f=classify('theorem f : {T : Type} → (x : T) → x = x')
        self.assertEqual(f['arrow_count_in_result'],2)
        self.assertNotIn('hypotheses',f)

    def test_closed_surface_stays_unproved(self):
        f=classify('theorem fixture : True')
        self.assertEqual(f['syntax_class'],'no-declaration-binders')

    def test_marker_in_result_does_not_imply_premise(self):
        f=classify('theorem f : ∃ x, Represented x')
        self.assertEqual(f['surface_markers'],['Represented'])
        self.assertIn('not a premise',f['marker_boundary'])

if __name__=='__main__': unittest.main()
