import unittest
from source_census import binder_groups, peel_result, source_shape, structure_fields
from census import mask

class SourceCensusTests(unittest.TestCase):
    def test_quantified_premise_is_not_parameter_names(self):
        nodes,tail,_ = peel_result('∀ xs ys, (∀ a, a ∈ xs → P a) → xs = ys → Q xs')
        self.assertEqual(nodes[0]['names'],['xs','ys'])
        self.assertEqual(nodes[1]['kind'],'leading-arrow-domain')
        self.assertEqual(nodes[1]['names'],[])
        self.assertEqual(tail,'Q xs')

    def test_dependent_arrow_and_nested_result_boundary(self):
        nodes,tail,_ = peel_result('(n : Nat) → A n ∧ (B n → C n)')
        self.assertEqual(len(nodes),1)
        self.assertEqual(nodes[0]['names'],['n'])
        self.assertEqual(tail,'A n ∧ (B n → C n)')

    def test_let_not_ne_are_not_silently_assumptions(self):
        for text in ['let x := y; P x → Q x','¬ (P → Q)','a ≠ b']:
            nodes,_,_ = peel_result(text)
            self.assertEqual(nodes,[])

    def test_annotation_beats_rhs_style(self):
        self.assertEqual(source_shape('Prop',set(),set()),'predicate-or-proposition-sort')
        self.assertEqual(source_shape('Bool',set(),set()),'operational-or-data-type-annotation')
        self.assertEqual(source_shape('Expr',set(),set()),'operational-or-data-type-annotation')
        self.assertEqual(source_shape('Cert p',set(),{'Cert'}),'named-proof-bearing-record-source')
        self.assertEqual(source_shape('ch.parse.Cert',set(),{'Cert'}),'named-or-dependent-type-needs-semantic-review')

    def test_fields_stop_at_deriving_or_commands(self):
        src = '\n  proof : Expr\n  certified : Bool\n  deriving Repr\n#check something\n'
        fields = structure_fields(src,mask(src),0,len(src))
        self.assertEqual([(f['source_field_label'],f['type_source']) for f in fields],[('proof','Expr'),('certified','Bool')])

    def test_existential_and_iff_scope_precede_arrow_peeling(self):
        for text in ['∃ x, P x → Q x','P → Q ↔ R','if flag then P → Q else R']:
            nodes,tail,_ = peel_result(text)
            self.assertEqual(nodes,[])
            self.assertEqual(tail,text)

    def test_let_in_type_is_not_a_default(self):
        groups,_ = binder_groups('(actual : let b := artifact; Exec b result)')
        self.assertEqual(groups[0]['type_source'],'let b := artifact; Exec b result')
        self.assertIsNone(groups[0]['default_source'])

    def test_literals_preserved_without_parsing_their_punctuation(self):
        groups,_ = binder_groups('(h : s = "a→b") (s : String := "[):=]")')
        self.assertEqual(groups[0]['type_source'],'s = "a→b"')
        self.assertEqual(groups[1]['default_source'],'"[):=]"')
        nodes,tail,_ = peel_result('(h : s = "a→b") → Q "x→y"')
        self.assertEqual(nodes[0]['type_source'],'s = "a→b"')
        self.assertEqual(tail,'Q "x→y"')

    def test_implicit_instance_and_default_binders(self):
        groups,used = binder_groups('{T : Type} [h : Inhabited T] (n : Nat := 1) : Q n')
        self.assertEqual(groups[1]['binder_style'],'instance')
        self.assertEqual(groups[2]['default_source'],'1')
        self.assertEqual(groups[2]['type_source'],'Nat')
        self.assertTrue('Q n' in '{T : Type} [h : Inhabited T] (n : Nat := 1) : Q n'[used:])

if __name__ == '__main__':
    unittest.main()
