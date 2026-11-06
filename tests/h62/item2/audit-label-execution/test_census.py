"""Scanner regressions for false frozen-statement coverage claims (no Lean)."""
import importlib.util
import copy
import json
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('census', ROOT/'scripts/h62/item2/audit-label-execution/census.py')
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)

class CensusTests(unittest.TestCase):
    def test_nested_comments_and_strings_preserve_offsets(self):
        source = '/- theorem false := /- nested -/ end -/\n"theorem fake :="\nnamespace N\ntheorem actual (n : Nat := 0) : n = n := by rfl\nend N\n'
        masked = census.mask(source)
        self.assertEqual(len(masked),len(source))
        rows = census.declarations(source,'Fixture.lean')
        self.assertEqual([r['name'] for r in rows],['N.actual'])
        self.assertTrue(rows[0]['signature'].endswith('n = n'))

    def test_result_lets_and_binder_defaults_are_not_proof_delimiters(self):
        source = 'namespace A\nsection\ntheorem t (n : Nat := 1) :\n let x := n; let y := x + 1; y = n + 1 := by rfl\nend\nend A\n'
        rows = census.declarations(source,'Fixture.lean')
        self.assertEqual(rows[0]['name'],'A.t')
        self.assertEqual(rows[0]['signature'],'theorem t (n : Nat := 1) :\n let x := n; let y := x + 1; y = n + 1')

    def test_brace_expansion_retains_empty_alternative(self):
        self.assertEqual(census.expand_braces('A/{B,C}{,Controls}.lean'),
                         ['A/B.lean','A/BControls.lean','A/C.lean','A/CControls.lean'])

    def test_frozen_blob_guard_rejects_local_mutation(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td); (root/'a.lean').write_bytes(b'modified')
            with patch.object(census.subprocess,'check_output',return_value=b'frozen'):
                with self.assertRaisesRegex(ValueError,'differs from worktree'):
                    census.frozen_bytes(root,'a.lean')
                (root/'a.lean').write_bytes(b'frozen')
                self.assertEqual(census.frozen_bytes(root,'a.lean'),b'frozen')

    def test_ambiguous_owners_are_retained(self):
        registry={'items':[{'id':n,'owner':n,'group':'h30-file-ownership','writeScope':'Solidity/A/**'} for n in ['one','two']]}
        self.assertEqual(len(census.owners('Solidity/A/B.lean',registry)),2)

    def test_frozen_real_map_completeness(self):
        paths=census.modules(ROOT)
        self.assertEqual(len(paths),147)
        rows=[r for p in paths for r in census.declarations(census.frozen_bytes(ROOT,p).decode(),p)]
        self.assertEqual(len(rows),656)
        self.assertEqual(len({(r['path'],r['name']) for r in rows}),656)
        # All eight real result-type let regressions now include the result after :=.
        affected=['bare_code_handled','loop_exit_step','source_body_fields','allocation_roundtrip','source_target_clipped_hash']
        for row in rows:
            if row['source_name'] in affected or row['path'].endswith(('ConditionalSequenceCompiler.lean','ConditionalSourceCompiler.lean','Lowering/G19/ConditionalSequence.lean')) and row['source_name']=='correct':
                self.assertIn(':=',row['signature'])
                self.assertFalse(row['signature'].endswith('Bool'))

class SourceBundleTests(unittest.TestCase):
    def test_inferred_and_instance_binders_stay_distinct(self):
        bundle=census.source_bundle('theorem t {α} [inst : Inhabited α] (n : Nat := 0) : n = n')
        bs=bundle['header_binders']
        self.assertEqual(bs[0]['names'],['α'])
        self.assertIsNone(bs[0]['type_source'])
        self.assertEqual(bs[0]['role_hint'],'inferred-parameter-group')
        self.assertEqual(bs[1]['binder_syntax'],'instance')
        self.assertEqual(bs[2]['type_source'],'Nat := 0')
        self.assertNotEqual(bs[2]['role_hint'],'per-input-condition')

    def test_named_argument_is_not_an_equality_premise(self):
        self.assertNotEqual(census.source_role('Source.Data.Inner (E:=E) data')[0],'per-input-condition')
        bundle=census.source_bundle('theorem t (checked : f (C := C) x = some y) : True')
        self.assertEqual(bundle['header_binders'][0]['role_hint'],'per-input-condition')
        self.assertEqual(bundle['header_binders'][0]['type_source'],'f (C := C) x = some y')

    def test_quantified_result_does_not_become_header_assumptions(self):
        bundle=census.source_bundle('theorem t : ∀ n, P n → ∀ m, Q m')
        self.assertEqual(bundle['header_binders'],[])
        self.assertEqual(bundle['result_source'],'∀ n, P n → ∀ m, Q m')
        self.assertTrue(bundle['result_begins_forall'])
        self.assertEqual(bundle['simultaneous_witness'],'pending')

    def test_comment_and_string_words_do_not_classify_a_type(self):
        self.assertEqual(census.source_role('Nat /- ∀ BoolSlot = x -/')[0],'argument-or-unresolved-bundle')

    def test_global_context_relation_and_quantified_law_are_distinct(self):
        self.assertEqual(census.source_role('Source.Glob E')[0],'global-environment-carrier')
        self.assertEqual(census.source_role('(x : T) → (y : U) → Prop')[0],'predicate-or-relation-parameter')
        self.assertEqual(census.source_role('∀ x, R x → P x')[0],'quantified-or-function-bundle')
        self.assertEqual(census.source_role('BoolSlot E')[0],'indexed-or-structured-bundle')

class ReconciliationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        directory=ROOT/'tests/h62/item2/audit-label-execution'
        cls.registry=json.loads(Path('/workspace/h62-coordinator-inputs/ownership.json').read_text())
        cls.reconciliation=json.loads((directory/'owner-reconciliation.json').read_text())
        cls.reviews=json.loads((directory/'source-bundle-reviews.json').read_text())
        cls.result=census.run(ROOT,cls.registry,cls.reconciliation,cls.reviews)

    def test_exact_attribution_does_not_invent_reservations_or_proofs(self):
        counts=self.result['counts']
        self.assertEqual(counts['declarations'],656)
        self.assertEqual(counts['producer_attribution_unresolved'],0)
        self.assertEqual(counts['owner_unresolved'],51)
        missing=[r for r in self.result['declarations'] if not r['owner_evidence']]
        self.assertEqual(len(missing),51)
        self.assertEqual(len({r['path'] for r in missing}),17) # one of 18 files is an import-only module
        for row in self.result['declarations']:
            self.assertEqual(row['simultaneous_witness'],'pending')
            self.assertEqual(row['statement_fidelity'],'pending')
            self.assertEqual(row['source_premise_bundle']['classification_level'],'source-routing-only')
        for row in missing:
            self.assertFalse(row['producer_attribution']['exact_file_h30_reservation_present'])
            self.assertIn('none granted',row['producer_attribution']['write_authorization'])

    def test_wrong_live_producer_is_rejected(self):
        bad=copy.deepcopy(self.reconciliation)
        bad['files'][0]['live_producer']='SYNTHETIC-WRONG-PRODUCER'
        with self.assertRaisesRegex(ValueError,'live producer mapping mismatch'):
            census.reconcile_owners(ROOT,self.registry,self.result['files'],self.result['declarations'],bad)

    def test_review_cannot_claim_witness_or_change_frozen_signature(self):
        for field,value,message in [('simultaneous_witness','verified','cannot certify'),('signature_sha256','0'*64,'signature mismatch')]:
            bad=copy.deepcopy(self.reviews);bad['declarations'][0][field]=value
            with self.assertRaisesRegex(ValueError,message):
                census.apply_source_reviews(ROOT,copy.deepcopy(self.result['declarations']),bad)

    def test_signature_bound_review_covers_subtle_actual_statements(self):
        reviewed={r['name']:r for r in self.result['declarations'] if 'source_review' in r}
        self.assertEqual(len(reviewed),10)
        integer=reviewed['Solidity.Yul.RawIntegerInitialization.correct']['source_premise_bundle']
        self.assertEqual(integer['header_binders'],[])
        self.assertIn('inRange',integer['result_source'])
        allocated=reviewed['Solidity.Yul.Adapters.AllocatedComputedFrame.allocated_supported']['source_premise_bundle']
        old=next(b for b in allocated['header_binders'] if b['names']==['old'])
        self.assertIn('→',old['type_source'])
        self.assertTrue(allocated['result_begins_forall'])
        capacity=reviewed['Solidity.Backend.LabelExec.BlockShape.control_capacity']['source_premise_bundle']
        self.assertIn('| _ => True',capacity['result_source'])

class LeadingForallTests(unittest.TestCase):
    def test_result_binder_order_and_separate_header(self):
        b=census.source_bundle('theorem t (n : Nat) : ∀ (m : Nat) (h : n = m), Q m')
        self.assertEqual([x['names'] for x in b['header_binders']],[['n']])
        q=b['leading_result_quantifiers']
        self.assertEqual([x['names'] for x in q['groups'][0]['source_binders']],[['m'],['h']])
        self.assertEqual(q['remaining_source'].strip(),'Q m')
        self.assertEqual(b['simultaneous_witness'],'pending')

    def test_bounded_source_is_not_invented_as_an_assumption(self):
        b=census.source_bundle('theorem t : ∀ n ∈ byteQuery bytes, n < 256')
        q=b['leading_result_quantifiers']['groups'][0]
        self.assertEqual(q['source'],'∀ n ∈ byteQuery bytes,')
        self.assertEqual(q['source_binders'],[])
        self.assertEqual(q['parse_status'],'bounded-notation-retained-for-elaboration')
        self.assertEqual(b['header_binders'],[])

    def test_arrow_stops_leading_quantifier_partition(self):
        q=census.source_bundle('theorem t : ∀ x : Nat, P x → ∀ y, Q x y')['leading_result_quantifiers']
        self.assertEqual(len(q['groups']),1)
        self.assertIn('→ ∀ y',q['remaining_source'])
        self.assertTrue(q['has_remaining_quantifier'])

    def test_comments_do_not_shift_unbracketed_type_offsets(self):
        q=census.source_bundle('theorem t : ∀ /- note -/ x : Nat, Q x')['leading_result_quantifiers']
        b=q['groups'][0]['source_binders'][0]
        self.assertEqual(b['names'],['x'])
        self.assertEqual(b['type_source'],'Nat')

    def test_result_lets_and_nested_quantifiers_stay_intact(self):
        b=census.source_bundle('theorem t : let z := 0; P z ∧ (∀ n, Q n)')
        self.assertEqual(b['leading_result_quantifiers']['groups'],[])
        self.assertEqual(b['leading_result_quantifiers']['remaining_source'],b['result_source'])
        self.assertTrue(b['leading_result_quantifiers']['has_remaining_quantifier'])

    def test_all_modules_and_quantifiers_are_accounted_exactly_once(self):
        ReconciliationTests.setUpClass()
        result=ReconciliationTests.result
        self.assertEqual(len(result['files']),147)
        identities=[(f['path'],r['name']) for f in result['files'] for r in f['source_summary']['declared_statement_identities']]
        self.assertEqual(len(identities),656)
        self.assertEqual(len(set(identities)),656)
        self.assertEqual(sum(f['source_summary']['header_binder_groups'] for f in result['files']),1914)
        self.assertEqual(sum(f['source_summary']['result_binder_groups'] for f in result['files']),513)
        self.assertEqual(sum(f['source_summary']['leading_result_quantifier_groups'] for f in result['files']),88)
        zero=[f for f in result['files'] if f['source_summary']['zero_direct_declarations']]
        self.assertEqual(len(zero),6)
        self.assertTrue(any(f['path']=='Solidity/Frontend/Yul/Parsing.lean' for f in zero))
        self.assertTrue(all(f['source_summary']['simultaneous_witnesses']==0 for f in result['files']))

class OverlayInspectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        p=ROOT/'scripts/h62/item2/audit-label-execution/inspect_overlay.py'
        spec=importlib.util.spec_from_file_location('inspect_overlay',p)
        cls.inspector=importlib.util.module_from_spec(spec)
        with patch.dict(sys.modules,{'census':census}):spec.loader.exec_module(cls.inspector)

    def header(self):
        p=self.inspector.PATH
        return f'diff --git a/{p} b/{p}\nindex 1234567..7654321 100644\n--- a/{p}\n+++ b/{p}\n'

    def test_actual_routed_overlay_is_inspected_without_application(self):
        r=self.inspector.inspect(ROOT,ROOT/'tests/h62/item2/audit-label-execution/owner-overlays/hash-partial-receipt.json')
        self.assertEqual(r['source_signatures_unchanged'],64)
        self.assertEqual(r['patch_sha256'],'3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff')
        self.assertFalse(r['overlay_applied'])
        self.assertFalse(r['lean_executed'])

    def test_relocated_artifact_still_requires_the_exact_routed_checksum(self):
        with tempfile.TemporaryDirectory() as directory:
            bad=Path(directory)/'wrong.patch';bad.write_text('not the routed artifact')
            with self.assertRaisesRegex(ValueError,'checksum mismatch'):
                self.inspector.inspect(ROOT,ROOT/'tests/h62/item2/audit-label-execution/owner-overlays/hash-partial-receipt.json',bad)

    def test_out_of_range_and_zero_count_hunks_are_rejected(self):
        for hunk in ['@@ -99,0 +2,1 @@\n+b\n','@@ -99,1 +1,1 @@\n-a\n+b\n']:
            with self.assertRaises(ValueError):self.inspector.apply_in_memory('a\n',self.header()+hunk)

    def test_contradictory_metadata_is_rejected(self):
        malformed=self.header().replace('--- a/','deleted file mode 100644\n--- a/',1)+'@@ -1,1 +1,1 @@\n-a\n+b\n'
        with self.assertRaisesRegex(ValueError,'metadata'):self.inspector.apply_in_memory('a\n',malformed)

    def test_wrong_context_and_hunk_counts_are_rejected(self):
        for hunk in ['@@ -1,1 +1,1 @@\n-x\n+b\n','@@ -1,1 +1,2 @@\n-a\n+b\n']:
            with self.assertRaises(ValueError):self.inspector.apply_in_memory('a\n',self.header()+hunk)

if __name__ == '__main__': unittest.main()
