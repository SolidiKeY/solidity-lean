import Solidity.Lowering.G17.Conditional
import Solidity.Lowering.G17.ShortCircuitControls

/-! Concrete conditional controls reject eager evaluation, branch reversal,
condition-effect loss and ignored failures. Existing heterogeneous P12 worlds
are reused; no heap/address relation is invented. -/
namespace Solidity.Lowering.G17.ConditionalControls
open V07 V07.P12NextInterface Source.SemanticsExamples
open V07.P12Controls (C E SrcCtx TgtCtx source target mapping)
open V07.P12AssignedConditionControls (values worlds initial bool_reflect)
open V07.MixedAssignmentControls (globals)

private def assignment : Source.RExpr E SrcCtx .bool :=
  .assign (.local .here) (.local (.there .here))
private def reverseAssignment : Source.RExpr E SrcCtx .bool :=
  .assign (.local (.there .here)) (.local .here)
private def failing : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons .revert .nil,.val (.simple (.bool false))⟩

def producer (p : Roadmap.Pipeline) (checked choice : Bool) :=
  conditionalCondition (globals p) {F0 with checked := checked} mapping values worlds
    (.bool choice) assignment reverseAssignment
    (P12AtomicConditions.literal (globals p) {F0 with checked := checked} mapping values worlds
      choice ⟨source,target,initial⟩)
    (P12AssignedConditionControls.producer p checked)
    (P12AssignedCondition.assignment (globals p) {F0 with checked := checked} mapping values worlds
      bool_reflect ⟨source,target,initial⟩ (.there .here) .here (.there .here) .here rfl rfl)

/-- Both branch choices execute real Source assignments, with distinct reached
locals and transported target alignment, for both pipelines/check modes. -/
theorem source_witness (p : Roadmap.Pipeline) (checked choice : Bool) (fuel : Nat) :
    let after : Source.EMState E SrcCtx :=
      if choice then (source.1.set .here (.bool true),source.2)
      else (source.1.set (.there .here) (.bool false),source.2)
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+3)
      (.cond (.bool choice) assignment reverseAssignment)).run source = (.ok (.val (.bool choice)),after) ∧
    ∃ out : Out C target.H TgtCtx, (producer p checked choice).operand.run target =
      .ok (out,.prim choice) ∧ Aligned mapping values worlds after out.st := by
  dsimp only
  have run : (Source.evalE (globals p) {F0 with checked := checked} (fuel+3)
      (.cond (.bool choice) assignment reverseAssignment)).run source =
      (.ok (.val (.bool choice)),if choice then (source.1.set .here (.bool true),source.2)
        else (source.1.set (.there .here) (.bool false),source.2)) := by
    rw [Source.evalE,Source.Hoare.run_bind,P12AtomicConditions.literal_source_run]
    dsimp only []
    rw [Source.Hoare.run_bind,source_getV_run]
    cases choice
    · exact source_assign_local_run (globals p) {F0 with checked := checked} fuel source
        (.there .here) .here _ rfl
    · exact source_assign_local_run (globals p) {F0 with checked := checked} fuel source
        .here (.there .here) _ rfl
  exact ⟨run,(producer p checked choice).success (fuel+3) source _ target choice initial run⟩

/-- A live condition write must be visible to the selected branch. Reading
that branch from the initial state would return false instead of true. -/
theorem reached_effect_witness :
    (conditionalOperand (assignLocalOperand .here (.there .here))
      (assignLocalOperand (.there .here) .here) failing).run target =
      .ok (⟨(target.setLocal .here true).setLocal (.there .here) true,List.prefix_refl _⟩,.prim true) := by
  rw [conditionalOperand_run,assigned_condition_operand_run]
  rfl

/-- Each choice skips a failing unselected branch. Selecting that same branch,
or failing the condition before selection, must propagate its halt. -/
theorem halt_selection (choice : Bool) :
    (conditionalOperand (P12AtomicConditions.literalOperand choice)
      (if choice then P12AtomicConditions.literalOperand true else failing)
      (if choice then failing else P12AtomicConditions.literalOperand true)).run target =
        .ok (⟨target,List.prefix_refl _⟩,.prim true) ∧
    (conditionalOperand (P12AtomicConditions.literalOperand choice)
      (if choice then failing else P12AtomicConditions.literalOperand true)
      (if choice then P12AtomicConditions.literalOperand true else failing)).run target = .error .revert ∧
    (conditionalOperand failing (P12AtomicConditions.literalOperand true)
      (P12AtomicConditions.literalOperand false)).run target = .error .revert := by
  cases choice <;> constructor
  all_goals first
    | rw [conditionalOperand_run,P12AtomicConditions.literal_native_run]; rfl
    | constructor
      · rw [conditionalOperand_run,P12AtomicConditions.literal_native_run]; rfl
      · rw [conditionalOperand_run]; rfl

#print axioms source_witness
#print axioms reached_effect_witness
#print axioms halt_selection
end Solidity.Lowering.G17.ConditionalControls
