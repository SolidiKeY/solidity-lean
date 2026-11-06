#!/usr/bin/env python3
"""Source classification acceptance; no Lean feasibility claim."""
import json
import subprocess
import tempfile
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-v09-passes"))
import premises


class PremiseAcceptance(unittest.TestCase):
    def test_outer_return_syntax_does_not_supply_premises(self):
        self.assertEqual(premises.return_frontier("∃ x, P x ∧ ∀ tail, Q x tail"), "existential-result; witnesses-are-outputs")
        self.assertEqual(premises.return_frontier("∀ tail, run code tail = result"), "universal-result; binder-inclusion-review-required")
        self.assertEqual(premises.return_frontier("let x := state; P x"), "let-prefixed-result; reduction-review-required")
        self.assertEqual(premises.return_frontier("let x := state; type_of% (f x)"), "macro-expansion-required")
        self.assertIn("no-hypothesis-absence", premises.return_frontier("P → Q"))

    def test_residual_constraint_distinctions(self):
        self.assertEqual(premises.constraint_form("Memory.compileProg b F P = some left"), "compiler-acceptance-equation")
        self.assertEqual(premises.constraint_form("b + Memory.frameNeedProg Q ≤ frame"), "frame-or-arena-bound")
        self.assertEqual(premises.constraint_form("tail.length + 2 ≤ 1024"), "stack-capacity-bound")
        self.assertEqual(premises.constraint_form("t.lo ≤ x ∧ x ≤ t.hi"), "numeric-range-bound")
        self.assertEqual(premises.constraint_form("unknown x"), "unresolved-source-form")

    def test_macro_callee_tokens_do_not_claim_resolution(self):
        heads = premises.macro_heads("let x := 0; type_of% ((Controls.f x))")
        self.assertEqual([h["token"] for h in heads], ["Controls.f"])
        self.assertIn("require resolution", heads[0]["resolution"])
        source = "let x := 0; type_of% ((Controls.f x))"
        a, b = heads[0]["token_span_in_return_type"]
        self.assertEqual(source[a:b], "Controls.f")

    def test_nested_binders_and_return_type_preserved(self):
        statement = "theorem t {C : Contract} (h : (f (a := x)) = y) : ∀ tail, let m := {x with v := tail}; P m → Q m"
        groups, result = premises.telescope(statement)
        self.assertEqual([b["names"] for b in groups], [["C"], ["h"]])
        self.assertEqual(groups[1]["type"], "(f (a := x)) = y")
        self.assertEqual(result, "∀ tail, let m := {x with v := tail}; P m → Q m")

    def test_scoped_variables_pop_at_namespace_end(self):
        source = "variable {a : Nat}\nnamespace A\nvariable {b : Bool}\nsection s\nvariable {c : Int}\ntheorem inside : True := by trivial\nend s\ntheorem outer : True := by trivial\nend A\ntheorem root : True := by trivial\n"
        available = lambda at: [b["names"] for b in premises.scoped_variables(source, source.index(at))]
        self.assertEqual(available("theorem inside"), [["a"], ["b"], ["c"]])
        self.assertEqual(available("theorem outer"), [["a"], ["b"]])
        self.assertEqual(available("theorem root"), [["a"]])

    def test_source_target_and_quantified_laws_not_conflated(self):
        role, _ = premises.classify("run (a.code ++ d.code) m = .ok final 0")
        self.assertIn("layer-unresolved", role)
        role, _ = premises.classify("∀ o, P.run σ = .ok o → AllocationInput b frame (cost σ) σ base m")
        self.assertEqual(role, "quantified-law; scope-unresolved")

    def test_assignment_tokens_are_not_equalities(self):
        role, _ = premises.classify("(checked (C := C) b F).Input L frame base state machine")
        self.assertEqual(role, "per-input-admission")
        role, _ = premises.classify("CustomType (f := fun x => x)")
        self.assertEqual(role, "unresolved-type; data-or-premise-not-inferred")

    def test_global_certificate_and_per_input_relation(self):
        self.assertEqual(premises.classify("CompiledVal b F e")[0], "global-program-certificate")
        self.assertEqual(premises.classify("StateRepr L b frame F σ base m")[0], "per-input-representation")
        self.assertEqual(premises.classify("MappedBoundaryLink a d L frame base σ m")[0], "per-input-reached-transport")
        self.assertEqual(premises.classify("Nat → Fin W")[0], "per-input-address-map-data-candidate")
        self.assertEqual(premises.classify("Backend.Scalar.BinaryInvocation c a b tail")[0], "per-input-stack-capacity-certificate")

    def test_generated_join_absolute_spans_and_unproved_status(self):
        with tempfile.TemporaryDirectory() as temporary:
            subprocess.run([sys.executable, str(ROOT / "scripts/h62/item2/audit-v09-passes/premises.py"),
                            "--output", temporary], check=True, stdout=subprocess.PIPE)
            result = json.loads((Path(temporary)/"premises.json").read_text())
        frozen = premises.census(ROOT)
        key = lambda r: (r["path"], r["name"], r["signature_sha256"], r["source_sha256"])
        self.assertEqual({key(r) for r in result["declarations"]}, {key(r) for r in frozen["declarations"]})
        self.assertEqual(len(result["declarations"]), 1259)
        for row in result["declarations"]:
            self.assertIsNone(row["simultaneous_witness"])
            self.assertEqual(row["witness_status"], "uncovered")
            source = (ROOT/row["path"]).read_text()
            for binder in row["source_binders"] + row["available_section_variables"]:
                a, b = binder["absolute_span"]
                self.assertEqual(source[a:b], binder["source"])
                self.assertEqual(binder["inhabitation"], "unproved")
                self.assertNotIn("source-execution", binder["source_role"])
        reflected = next(r for r in result["declarations"] if r["name"] == "Solidity.Backend.Passes.compilation_mapped_reflect_success")
        ht = next(b for b in reflected["source_binders"] if b["names"] == ["ht"])
        self.assertIn("layer-unresolved", ht["source_role"])
        self.assertEqual(result["summary"]["witnesses_verified"], 0)

    def test_every_frozen_telescope_and_available_group(self):
        inventory = premises.census(ROOT)
        groups, context, no_groups, macros = 0, 0, 0, 0
        for row in inventory["declarations"]:
            binders, conclusion = premises.telescope(row["signature"])
            source = (ROOT / row["path"]).read_text()
            start, end = row["character_span"]
            offset = start + len(source[start:end]) - len(source[start:end].lstrip())
            variables = premises.scoped_variables(source, start)
            groups += len(binders)
            context += len(variables)
            no_groups += not binders
            macros += "type_of%" in conclusion
            self.assertTrue(conclusion)
            for binder in binders:
                a, b = binder["span"]
                self.assertEqual(source[offset+a:offset+b], binder["source"])
            for binder in variables:
                a, b = binder["span"]
                self.assertEqual(source[a:b], binder["source"])
        self.assertEqual((len(inventory["declarations"]), groups, context, no_groups, macros),
                         (1259, 1327, 427, 820, 27))


if __name__ == "__main__":
    unittest.main()
