import Solidity.Lowering.V08.ConditionalCallable

/-! Guards the regression where conditional-call selection, typed alignment and
read premises are witnessed on different callers. All public transport_context
premises below hold simultaneously in the existing signed-int8 fixture, for both
choices and arbitrary base states. State.init also supplies an actual base.
This does not establish arbitrary callee compilation, ABI or SourceSpec admission. -/
namespace H62.AuditV08Adapters.ConditionalCallableJoint
open Solidity Source
open Solidity.Lowering.V07 Solidity.Lowering.V08
open ConditionalCallable.Controls
open SignedCallableControls

/-- All propositional hypotheses of this exact transport_context instance.
The SAME locals, base, selected global, mapping and choice occur throughout. -/
def Joint {C : Contract} (base : State C []) (p : Roadmap.Pipeline) (choice : Bool) : Prop :=
  IntegerCallable.Inputs (global p) frame declaration t ∧
  slots.Related AssignedCallableContext.Values (locals choice) (target base choice).env ∧
  (∀ (v : Source.Val E.layout .bool) (c : Bool),
    AssignedCallableContext.Values (C:=C) (H:=base.H) .bool (.val .bool) v c → v = .bool c) ∧
  slots.slot (.here : Source.Idx ctx .bool) = ⟨.val .bool,tci⟩ ∧
  slots.slot (.there .here : Source.Idx ctx .bool) = ⟨.val .bool,tca⟩ ∧
  slots.slot destination = ⟨.val (integerPrim t),ti⟩ ∧
  slots.slot left = ⟨.val (integerPrim t),ta⟩ ∧
  slots.slot destination = ⟨.val (integerPrim t),ti⟩ ∧
  slots.slot right = ⟨.val (integerPrim t),tb⟩ ∧
  (t.lo ≤ chosen choice ∧ chosen choice ≤ t.hi) ∧
  (locals choice).get (.there .here : Source.Idx ctx .bool) = .bool choice ∧
  ((locals choice).set (.here : Source.Idx ctx .bool) (.bool choice)).get
    (if choice then left else right) = .int (chosen choice) (chosen_bound choice)

theorem joint {C : Contract} (base : State C []) (p : Roadmap.Pipeline) (choice : Bool) :
    Joint base p choice := by
  refine ⟨inputs p, initial_alignment base choice, (fun _ _ h => h),
    rfl, rfl, rfl, rfl, rfl, rfl, chosen_bound choice, rfl, ?_⟩
  cases choice <;> rfl

/-- The whole joint predicate has an actual target base, not only a conditional
inhabitant requiring somebody else to supply State C []. -/
theorem inhabited (p : Roadmap.Pipeline) (choice : Bool) :
    ∃ base : State ConstructorScalarTransport.Cell [], Joint base p choice :=
  ⟨State.init _, joint _ p choice⟩

/-- Full original conditional transport instance, including value relation and
reached caller alignment, for the same model. No desired run is a hypothesis. -/
theorem actual {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (extra : Nat) (bytes : Roadmap.Bytes) (choice : Bool) :
    (Source.evalE (global p) frame (extra+17) (expression p)).run (locals choice,populated bytes) =
      (.ok (.val (.int (chosen choice) (chosen_bound choice))),
        ConditionalAssignments.sourceAfter (locals choice,populated bytes)
          .here choice destination left destination right) ∧
    (ConditionalAssignments.operand tci tca ti ta ti tb).run (target base choice) =
      .ok (⟨ConditionalAssignments.targetAfter (target base choice) tci choice ti ta ti tb,
        List.prefix_refl _⟩,.prim (integerValue t (chosen choice) (chosen_bound choice))) ∧
    AssignedCallableContext.Values (C:=C) (H:=base.H) (.int t) (.val (integerPrim t))
      (.int (chosen choice) (chosen_bound choice)) (integerValue t (chosen choice) (chosen_bound choice)) ∧
    slots.Related AssignedCallableContext.Values
      (ConditionalAssignments.sourceAfter (locals choice,populated bytes)
        .here choice destination left destination right).1
      (ConditionalAssignments.targetAfter (target base choice) tci choice ti ta ti tb).env := by
  have execution := context_client base p extra bytes choice
  exact ⟨execution.1, execution.2.1, integer_related _ _ _, execution.2.2⟩

/-- An unchanged initial caller snapshot cannot stand in for the reached caller. -/
theorem stale_caller_refused {C : Contract} (base : State C []) :
    ¬ slots.Related AssignedCallableContext.Values (locals false)
      (ConditionalAssignments.targetAfter (target base false) tci false ti ta ti tb).env :=
  wrong_context_snapshot base

/-- Keeping only the condition write loses the selected branch's actual write. -/
theorem skipped_write_refused {C : Contract} (base : State C []) :
    ¬ slots.Related AssignedCallableContext.Values ((locals true).set .here (.bool true))
      (ConditionalAssignments.targetAfter (target base true) tci true ti ta ti tb).env :=
  skipped_branch_write base

#print axioms inhabited
#print axioms actual
#print axioms stale_caller_refused
#print axioms skipped_write_refused
end H62.AuditV08Adapters.ConditionalCallableJoint
