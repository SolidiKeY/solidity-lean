"""Semantic audit regressions: avoid counting conditions/absence as refusal."""
import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location("classify",Path(__file__).with_name("classify.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class ClassificationTest(unittest.TestCase):
    def test_quantified_result_is_not_closed_fixture(self):
        tree=m.proposition("∀ depth, f depth = g depth")
        self.assertEqual(m.input_regime("theorem law",[],"∀ depth, f depth = g depth",tree),"universal-result-parameters")
        self.assertEqual(m.input_regime("private def tree",[],"Nat → Nodes",None),"function-or-dependent-result-type")
    def test_validation_refuses_dropped_case(self):
        inventory={"declarations":[{"path":"Controls.lean","line":1}],"files":[{"path":"Controls.lean"}]}
        with self.assertRaises(ValueError): m.validate({"declarations":[],"files":[{"path":"Controls.lean"}]},inventory)
    def test_validation_refuses_duplicate_case(self):
        row={"path":"Controls.lean","line":1}
        inventory={"declarations":[row],"files":[{"path":"Controls.lean"}]}
        with self.assertRaises(ValueError): m.validate({"declarations":[row,row],"files":[{"path":"Controls.lean"}]},inventory)
    def test_comment_and_string_operators_ignored(self):
        for text in ('f = "a ∧ b"', 'f /- ∧ bogus -/ = g', 'f = "a → b = none"'):
            self.assertEqual(m.proposition(text)["form"],"equality")
    def test_generated_list_does_not_claim_readback(self):
        self.assertEqual(m.equality_meaning(m.proposition("demands v = [.word .nil]")),"whole-ordered-value-or-observation-equality")
    def test_implication_conditions_are_not_outcomes(self):
        rows=m.contract_semantics(m.proposition("failed = none → succeeds = some true"))
        self.assertEqual([(r["context"],r["contract"].get("right")) for r in rows],[("premise","none"),("asserted","some true")])
    def test_nested_absence_not_refusal(self):
        tree=m.proposition("out = some none")
        self.assertEqual(tree["expected_form"],"option-some")
        self.assertEqual(m.equality_meaning(tree),"partial-result-present-exact-payload-retained")
    def test_observation_not_operation_failure(self):
        self.assertEqual(m.equality_meaning(m.proposition("path.readLive Value.dflt value = none")),"unavailable-graph-observation")
        self.assertEqual(m.equality_meaning(m.proposition("(operationPush value).map readLive = none")),"composed-partial-result-none")
    def test_refusal_exact_published_boundary(self):
        p="Solidity.Backend.StorageOps.Published.pop 0 dead aliasPath = none"
        self.assertEqual(m.equality_meaning(m.proposition(p)),"published-fragment-refusal")
    def test_iff_negation_and_alternative_not_asserted_results(self):
        for text in ("a = none ↔ b = none","a = none ∨ b = none"):
            self.assertFalse(any(r["context"]=="asserted" and r["polarity"] and r["form"]=="equality" for r in m.contract_semantics(m.proposition(text))))
        rows=m.contract_semantics(m.proposition("¬ (a = none)"))
        self.assertFalse(next(r for r in rows if r["form"]=="equality")["polarity"])
    def test_lets_and_product_keep_whole_case(self):
        text="let x := before\n    let y := after\n    (view x, view y) = (some none, some true)"
        tree=m.proposition(text)
        rows=m.contract_semantics(tree)
        self.assertEqual(len(rows),1)
        self.assertEqual(rows[0]["meaning"],"whole-ordered-value-or-observation-equality")
    def test_semicolon_let_and_binder_arrow(self):
        params,result=m.declared_type("theorem t (f : Nat → Nat) : let x := f 0; x = x")
        self.assertIn("Nat → Nat",params)
        self.assertEqual(m.proposition(result)["body"]["form"],"equality")
    def test_quantifiers_keep_binders_and_nested_commas(self):
        tree=m.proposition("∃ x : Nat × Nat, ∀ i, f (x, i) = some true ∧ g i ≠ none")
        self.assertEqual(tree["form"],"exists")
        self.assertEqual(tree["body"]["form"],"forall")
        self.assertEqual([r["form"] for r in m.contract_semantics(tree)],["equality","inequality"])

if __name__=="__main__": unittest.main()
