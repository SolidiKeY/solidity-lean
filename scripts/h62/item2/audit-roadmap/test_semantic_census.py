import unittest
from semantic_census import body_first_line, family_index, classify_record

def record(name='N.f',kind='def',typ='Gen α'):
    return dict(source_qualified_name=name,kind=kind,result_type_source=typ,
        classification='dependent-or-inferred-result; semantic classification pending',line=1)

def family(head,id='fixture'):
    return dict(id=id,heads=[head],description='fixture source family',
        evidence=[],remaining='Payload and semantic obligations remain open.')

class SemanticCensusTests(unittest.TestCase):
    def test_exact_alias_expansion_and_no_discharge(self):
        r=record('N.Word','abbrev',None)
        a={'N.Word':dict(category='bounded-alias',expected_rhs='Fin 256',remaining='Bound proof is data, not a semantic law.')}
        out=classify_record(r,{},a,{},'abbrev Word := Fin 256\n')
        self.assertEqual(out['source_expansion'],'Fin 256')
        self.assertFalse(out['excludes_from_audit'])
        self.assertFalse(out['checked_witness_added'])
        self.assertFalse(out['elaborated_identity_claim'])

    def test_wrong_alias_rhs_rejected(self):
        a={'N.Word':dict(category='bounded-alias',expected_rhs='Fin 256',remaining='open')}
        with self.assertRaises(AssertionError):
            classify_record(record('N.Word','abbrev',None),{},a,{},'abbrev Word := Nat\n')

    def test_string_rhs_preserves_literal(self):
        self.assertEqual(body_first_line('private def n := "a:=b"\n',1),'"a:=b"')

    def test_unsupported_multiline_alias_fails_closed(self):
        with self.assertRaises(AssertionError):
            body_first_line('abbrev A :=\n  Nat\n',1)

    def test_unknown_result_family_rejected(self):
        with self.assertRaises(ValueError):
            classify_record(record(typ='Unknown X'),{}, {}, {}, '')

    def test_parametric_marker_is_not_a_proof_result(self):
        out=classify_record(record(),{'Gen':family('Gen')},{},{},'')
        self.assertTrue(out['syntactic_parametric_marker_present'])
        self.assertFalse(out['checked_witness_added'])
        self.assertTrue(out['residual_obligations'])

    def test_external_state_not_expanded(self):
        out=classify_record(record(typ='EVM.State'),{'EVM.State':family('EVM.State')},{},{},'')
        self.assertTrue(out['external_target_definition_not_expanded'])

    def test_fold_requires_concrete_codomain_review(self):
        with self.assertRaises(AssertionError):
            classify_record(record(typ='Fold'),{'Fold':family('Fold')},{},{},'')

    def test_namespace_sensitive_head_requires_review(self):
        with self.assertRaises(AssertionError):
            classify_record(record(typ='Word'),{'Word':family('Word')},{},{},'')

    def test_duplicate_head_catalog_rejected(self):
        with self.assertRaises(ValueError):
            family_index([family('Word'),family('Word')])

if __name__ == '__main__':
    unittest.main()
