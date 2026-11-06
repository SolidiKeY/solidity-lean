import Solidity.Backend.Selection.InterfaceV2

/-! Determinism of the existing finite structured target execution relation.
No target predicate, instruction semantics, source state or budget is changed. -/
namespace SolidityBridge.Yul.StructuredUnique
open Solidity Backend Scalar Selection

theorem output_unique {block : Backend.Block} {input first second : Scalar.Stack}
    (left : StructuredExec block input first) (right : StructuredExec block input second) :
    first = second := by
  induction left generalizing second with
  | code ran =>
    cases right with
    | code other => exact Option.some.inj (ran.symm.trans other)
  | seq before after ihBefore ihAfter =>
    cases right with
    | seq otherBefore otherAfter =>
      have same := ihBefore otherBefore
      subst same
      exact ihAfter otherAfter
  | iteTrue condition nonzero body ih =>
    cases right with
    | iteTrue otherCondition otherNonzero otherBody =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj (Option.some.inj (condition.symm.trans otherCondition))
      exact ih otherBody
    | iteFalse otherCondition otherBody =>
      have same := (List.cons.inj (Option.some.inj (condition.symm.trans otherCondition))).1
      exact False.elim (nonzero same)
  | iteFalse condition body ih =>
    cases right with
    | iteTrue otherCondition otherNonzero otherBody =>
      have same := (List.cons.inj (Option.some.inj (otherCondition.symm.trans condition))).1
      exact False.elim (otherNonzero same)
    | iteFalse otherCondition otherBody =>
      have same := (List.cons.inj (Option.some.inj (condition.symm.trans otherCondition))).2
      subst same
      exact ih otherBody
  | loopDone condition =>
    cases right with
    | loopDone otherCondition =>
      exact (List.cons.inj (Option.some.inj (condition.symm.trans otherCondition))).2
    | loopMore otherCondition otherNonzero otherBody otherRest =>
      have same := (List.cons.inj (Option.some.inj (otherCondition.symm.trans condition))).1
      exact False.elim (otherNonzero same)
  | loopMore condition nonzero body rest ihBody ihRest =>
    cases right with
    | loopDone otherCondition =>
      have same := (List.cons.inj (Option.some.inj (condition.symm.trans otherCondition))).1
      exact False.elim (nonzero same)
    | loopMore otherCondition otherNonzero otherBody otherRest =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj (Option.some.inj (condition.symm.trans otherCondition))
      have same := ihBody otherBody
      subst same
      exact ihRest otherRest

/-- info: 'SolidityBridge.Yul.StructuredUnique.output_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms output_unique
end SolidityBridge.Yul.StructuredUnique
