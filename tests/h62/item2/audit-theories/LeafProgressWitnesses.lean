import Solidity.Theory.Progress.Leaves
import Solidity.Source.SemanticsExamples

/-! Exact joint inputs for all six frozen leaf-extension statements. The
call-free global law is witnessed at EVERY horizon/frame, with an inhabited
frame predicate. It supplies no admitted internal function. Independently,
require(true) is an actual admitted extension node that succeeds for every
compatible source state under both pipelines. Fuel is not EVM gas. -/
namespace H62.AuditTheories
open Solidity Solidity.Source Solidity.Source.Progress Solidity.Theory.Progress
open Solidity.Source.SemanticsExamples

/-- A real builtin leaf with one evaluated boolean argument. -/
def leafRequire : RStmt E0 [] false .body [] [] :=
  .expr (.builtin .require (.cons (.bool true) .nil) rfl)

/-- The success control really belongs to the builtin extension. -/
theorem leaf_require_admitted : BuiltinNode (fun _ => False) leafRequire := by
  exact .mk .require (.cons (.bool true) .nil) rfl
    (.require _ (.cons (.checked _ trivial trivial) .nil))

/-- Total source success, not merely Ends: every compatible state, both pipelines. -/
theorem leaf_require_success (p : Roadmap.Pipeline) (st : St E0) :
    ((execS (G0 p) F0 8 0 none leafRequire .nil).run (.nil, st)).1 =
      .ok (.normal .nil) := by
  cases p <;> rfl

/-- An always-revert/error source runner cannot reproduce the observed success. -/
theorem leaf_require_excludes_error (p : Roadmap.Pipeline) (st : St E0) (halt : Halt) :
    ((execS (G0 p) F0 8 0 none leafRequire .nil).run (.nil, st)).1 ≠ .error halt := by
  rw [leaf_require_success]
  intro h
  cases h

/-- The low-fuel boundary is observable and separate from successful execution. -/
theorem leaf_require_fuel_boundary (p : Roadmap.Pipeline) (st : St E0) :
    ((execS (G0 p) F0 0 0 none leafRequire .nil).run (.nil, st)).1 = .error .timeout ∧
    ((execS (G0 p) F0 8 0 none leafRequire .nil).run (.nil, st)).1 = .ok (.normal .nil) :=
  ⟨rfl, leaf_require_success p st⟩

/-- The whole expression premise holds, including all horizons and all frames. -/
theorem leaf_all_expression_horizons :
    ∀ n F, (fun _ : String => True) F.contract → ExprNSAt (fun _ => False) (G0 .legacy) F n :=
  fun n F _ => exprNSAt (G0 .legacy) F n

/-- All frozen configuration inputs coexist with a real successful builtin leaf. -/
theorem leaf_emit_inputs_joint :
    ∃ (E : Env) (G : Glob E) (A : Decl → Prop) (Q : String → Prop) (F : Fr),
      Q F.contract ∧ ∃ (s : RStmt E [] false .body [] []) (st : St E),
        BuiltinNode A s ∧
        ((execS G F 8 0 none s .nil).run (.nil, st)).1 = .ok (.normal .nil) := by
  exact ⟨E0, G0 .legacy, (fun _ => False), (fun _ => True), F0, trivial, leafRequire, s0,
    leaf_require_admitted, leaf_require_success .legacy s0⟩

/-- All frozen configuration inputs coexist with a real successful builtin leaf. -/
theorem leaf_revert_error_inputs_joint :
    ∃ (E : Env) (G : Glob E) (A : Decl → Prop) (Q : String → Prop) (F : Fr),
      Q F.contract ∧ ∃ (s : RStmt E [] false .body [] []) (st : St E),
        BuiltinNode A s ∧
        ((execS G F 8 0 none s .nil).run (.nil, st)).1 = .ok (.normal .nil) := by
  exact ⟨E0, G0 .legacy, (fun _ => False), (fun _ => True), F0, trivial, leafRequire, s0,
    leaf_require_admitted, leaf_require_success .legacy s0⟩

/-- All frozen configuration inputs and the entire quantified premise coexist with a real successful builtin leaf. -/
theorem leaf_builtin_inputs_joint :
    ∃ (E : Env) (G : Glob E) (A : Decl → Prop) (Q : String → Prop) (F : Fr),
      (∀ n F, Q F.contract → ExprNSAt A G F n) ∧
      Q F.contract ∧ ∃ (s : RStmt E [] false .body [] []) (st : St E),
        BuiltinNode A s ∧
        ((execS G F 8 0 none s .nil).run (.nil, st)).1 = .ok (.normal .nil) := by
  exact ⟨E0, G0 .legacy, (fun _ => False), (fun _ => True), F0, leaf_all_expression_horizons, trivial, leafRequire, s0,
    leaf_require_admitted, leaf_require_success .legacy s0⟩

/-- All frozen configuration inputs and the entire quantified premise coexist with a real successful builtin leaf. -/
theorem leaf_all_inputs_joint :
    ∃ (E : Env) (G : Glob E) (A : Decl → Prop) (Q : String → Prop) (F : Fr),
      (∀ n F, Q F.contract → ExprNSAt A G F n) ∧
      Q F.contract ∧ ∃ (s : RStmt E [] false .body [] []) (st : St E),
        BuiltinNode A s ∧
        ((execS G F 8 0 none s .nil).run (.nil, st)).1 = .ok (.normal .nil) := by
  exact ⟨E0, G0 .legacy, (fun _ => False), (fun _ => True), F0, leaf_all_expression_horizons, trivial, leafRequire, s0,
    leaf_require_admitted, leaf_require_success .legacy s0⟩

/-- All frozen configuration inputs coexist with a real successful builtin leaf. -/
theorem leaf_effect_inputs_joint :
    ∃ (E : Env) (G : Glob E) (A : Decl → Prop) (Q : String → Prop) (F : Fr),
      Q F.contract ∧ ∃ (s : RStmt E [] false .body [] []) (st : St E),
        BuiltinNode A s ∧
        ((execS G F 8 0 none s .nil).run (.nil, st)).1 = .ok (.normal .nil) := by
  exact ⟨E0, G0 .legacy, (fun _ => False), (fun _ => True), F0, trivial, leafRequire, s0,
    leaf_require_admitted, leaf_require_success .legacy s0⟩

/-- All frozen configuration inputs coexist with a real successful builtin leaf. -/
theorem leaf_call_free_inputs_joint :
    ∃ (E : Env) (G : Glob E) (Q : String → Prop) (F : Fr),
      Q F.contract ∧ ∃ (s : RStmt E [] false .body [] []) (st : St E),
        BuiltinNode (fun _ => False) s ∧
        ((execS G F 8 0 none s .nil).run (.nil, st)).1 = .ok (.normal .nil) := by
  exact ⟨E0, G0 .legacy, (fun _ => True), F0, trivial, leafRequire, s0,
    leaf_require_admitted, leaf_require_success .legacy s0⟩

#print axioms leaf_require_admitted
#print axioms leaf_require_success
#print axioms leaf_require_excludes_error
#print axioms leaf_require_fuel_boundary
#print axioms leaf_all_expression_horizons
#print axioms leaf_emit_inputs_joint
#print axioms leaf_revert_error_inputs_joint
#print axioms leaf_builtin_inputs_joint
#print axioms leaf_all_inputs_joint
#print axioms leaf_effect_inputs_joint
#print axioms leaf_call_free_inputs_joint
end H62.AuditTheories
