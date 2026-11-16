import Solidity.Theory.Progress.Tuple
import tests.h62.item2.«audit-theories».ProgressWitnesses

/-! Joint inputs for the five ordinary frozen tuple-progress statements.
The public declaration constructor infers its exact slotsFit proof type on
each tree; that proof is packed, never replaced by SlotsOK alone. Global
expression progress covers every lower horizon for the SAME G/F/A. Real
nonempty tuple stages and two declared slots coexist. Val.not_tuple remains
an intentional H69 refutation, audited by the existing impossibility proof.
Source fuel and source pipelines are not physical EVM gas/fork/compiler claims. -/
namespace H62.AuditTheories
open Solidity Solidity.Source Solidity.Source.Progress Solidity.Theory.Progress
open Solidity.Source.SemanticsExamples EM

/-- Actual source arguments, with a false middle component discarded by the slots. -/
def tupleAuditArgs : RArgs E0 [] [.bool, .bool, .bool] :=
  .cons (.bool true) (.cons (.bool false) (.cons (.bool true) .nil))

/-- The corresponding runtime tuple components. -/
def tupleAuditVals : RVals E0.layout [.bool, .bool, .bool] :=
  .cons (.val (.bool true)) (.cons (.val (.bool false)) (.cons (.val (.bool true)) .nil))

/-- Two actual declared slots and one hole, not an empty arity witness. -/
def tupleAuditSlots : List (Option STy) := [some .bool, none, some .bool]

/-- Every argument is in the fragment, simultaneously. -/
theorem tuple_args_admitted : ArgsFragment (fun _ => False) tupleAuditArgs :=
  .cons (.checked _ trivial trivial) (.cons (.checked _ trivial trivial)
    (.cons (.checked _ trivial trivial) .nil))

/-- All slot conditions hold for the same component types. -/
theorem tuple_slots_admitted : SlotsOK tupleAuditSlots [.bool, .bool, .bool] :=
  ⟨rfl, .inl rfl, rfl, .inl rfl, trivial⟩

/-- Totality of three actual stages for every compatible source state and pipeline. -/
theorem tuple_stages_success (p : Roadmap.Pipeline) (st : St E0) :
    ((evalArgs (G0 p) F0 8 tupleAuditArgs).run (.nil, st)).1 = .ok tupleAuditVals ∧
    (RVal.tuple tupleAuditVals).untuple = .ok tupleAuditVals ∧
    ((pushVals (E := E0) (Γ' := []) F0 8 tupleAuditSlots tupleAuditVals .nil).run (.nil, st)).1 =
      .ok (.cons (.bool true) (.cons (.bool true) .nil)) := by
  cases p <;> exact ⟨rfl, rfl, rfl⟩

/-- All ordinary untuple inputs coexist, and untupling really returns components. -/
theorem tuple_untuple_inputs_joint :
    ∃ (D : Layout) (ts : List STy) (v : RVal D (.tuple ts)), ∃ vs, v.untuple = .ok vs :=
  ⟨E0.layout, [.bool, .bool, .bool], .tuple tupleAuditVals, tupleAuditVals, rfl⟩

/-- The constructor packs the EXACT slotsFit proof alongside SlotsOK, runtime
values, the output frame index and selected locals. Its OpsOK is extra support. -/
theorem tuple_push_inputs_joint :
    ∃ (E : Env) (Γ' : RCtx) (F : Fr) (n : Nat) (slots : List (Option STy))
      (ts : List STy) (vs : RVals E.layout ts) (Γ : RCtx) (l : Locals E.layout Γ)
      (es : RArgs E Γ ts) (x : Locals E.layout Γ' × St E),
      SlotsOK slots ts ∧ ∃ fit,
        (RStmt.declTuple (R := []) (M := false) (k := .body) slots (.tuple es) fit).OpsOK ∧
        ∃ result, ((pushVals (Γ' := Γ') F n slots vs l).run x).1 = .ok result := by
  refine ⟨E0, [], F0, 8, tupleAuditSlots, [.bool, .bool, .bool], tupleAuditVals,
    [], .nil, tupleAuditArgs, (.nil, s0), tuple_slots_admitted, (by decide), ?_,
    _, (tuple_stages_success .legacy s0).2.2⟩
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- The whole lower-horizon expression law coexists with later argument data,
fragment membership and an actual nonempty successful argument evaluation. -/
theorem tuple_args_inputs_joint :
    ∃ (E : Env) (A : Decl → Prop) (G : Glob E) (F : Fr) (Γ : RCtx) (n : Nat)
      (ts : List STy) (es : RArgs E Γ ts) (x : Locals E.layout Γ × St E),
      (∀ m, m ≤ n → ExprNSAt A G F m) ∧ ArgsFragment A es ∧
      ∃ vs, ((evalArgs G F n es).run x).1 = .ok vs := by
  exact ⟨E0, (fun _ => False), G0 .legacy, F0, [], 8, [.bool, .bool, .bool],
    tupleAuditArgs, (.nil, s0), (fun m _ => exprNSAt _ _ m), tuple_args_admitted,
    _, (tuple_stages_success .legacy s0).1⟩

/-- The same complete global law and literal initializer predicate hold at a
successful selected tuple expression, with every inherited context input. -/
theorem tuple_initializer_inputs_joint :
    ∃ (E : Env) (A : Decl → Prop) (G : Glob E) (F : Fr) (n : Nat) (Γ : RCtx)
      (ts : List STy) (e : RExpr E Γ (.tuple ts)) (x : Locals E.layout Γ × St E),
      (∀ m, m ≤ n → ExprNSAt A G F m) ∧ TupleInit A e ∧
      ∃ v, ((evalE G F n e).run x).1 = .ok v := by
  exact ⟨E0, (fun _ => False), G0 .legacy, F0, 8, [], [.bool, .bool, .bool],
    .tuple tupleAuditArgs, (.nil, s0), (fun m _ => exprNSAt _ _ m),
    .lit _ tuple_args_admitted, .tuple tupleAuditVals, rfl⟩

/-- Every declaration input and all four premise proofs are simultaneous.
The public constructor retains fit's exact frozen/current type without an alias
or a weakened fit predicate. Selected locals occur after that proof. -/
theorem tuple_declaration_inputs_joint :
    ∃ (E : Env) (A : Decl → Prop) (G : Glob E) (F : Fr) (n nps : Nat)
      (ph : Option (Ph E)) (R : List STy) (M : Bool) (k : SCtx) (Γ : RCtx)
      (ts : List STy) (slots : List (Option STy)) (e : RExpr E Γ (.tuple ts)),
      (∀ m, m ≤ n → ExprNSAt A G F m) ∧ TupleInit A e ∧ SlotsOK slots ts ∧
      ∃ fit, ∃ (l : Locals E.layout Γ) (x : Locals E.layout [] × St E),
        ∃ result, ((execS G F (n + 1) nps ph
          (RStmt.declTuple (R := R) (M := M) (k := k) slots e fit) l).run x).1 = .ok result := by
  exact ⟨E0, (fun _ => False), G0 .legacy, F0, 9, 0, none, [], false, .body,
    [], [.bool, .bool, .bool], tupleAuditSlots, .tuple tupleAuditArgs,
    (fun m _ => exprNSAt _ _ m), .lit _ tuple_args_admitted, tuple_slots_admitted,
    (by decide), .nil, (.nil, s0), .normal (.cons (.bool true) (.cons (.bool true) .nil)), rfl⟩

/-- An always-error source stage cannot reproduce either concrete successful stage. -/
theorem tuple_stages_exclude_error (p : Roadmap.Pipeline) (st : St E0) (halt : Halt) :
    ((evalArgs (G0 p) F0 8 tupleAuditArgs).run (.nil, st)).1 ≠ .error halt ∧
    ((pushVals (E := E0) (Γ' := []) F0 8 tupleAuditSlots tupleAuditVals .nil).run (.nil, st)).1 ≠
      .error halt := by
  constructor
  · rw [(tuple_stages_success p st).1]
    intro h
    cases h
  · rw [(tuple_stages_success p st).2.2]
    intro h
    cases h

/-- Positive-horizon source success is distinct from the zero-fuel boundary. -/
theorem tuple_stages_fuel_boundary (p : Roadmap.Pipeline) (st : St E0) :
    ((evalArgs (G0 p) F0 0 tupleAuditArgs).run (.nil, st)).1 = .error .timeout ∧
    ((evalArgs (G0 p) F0 8 tupleAuditArgs).run (.nil, st)).1 = .ok tupleAuditVals :=
  ⟨rfl, (tuple_stages_success p st).1⟩

#print axioms tuple_args_admitted
#print axioms tuple_slots_admitted
#print axioms tuple_stages_success
#print axioms tuple_untuple_inputs_joint
#print axioms tuple_push_inputs_joint
#print axioms tuple_args_inputs_joint
#print axioms tuple_initializer_inputs_joint
#print axioms tuple_declaration_inputs_joint
#print axioms tuple_stages_exclude_error
#print axioms tuple_stages_fuel_boundary

set_option pp.all true in #check @tuple_push_inputs_joint
set_option pp.all true in #check @tuple_declaration_inputs_joint
end H62.AuditTheories
