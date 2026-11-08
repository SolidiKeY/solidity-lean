import Solidity.Lowering.G17.Conditional
import Solidity.Lowering.G17.ShortCircuitControls
import Solidity.Lowering.G17.ShortCircuitRevertControls

/-! Concrete conditional controls reject eager evaluation, branch reversal, condition-effect loss and ignored failures. Existing heterogeneous P12 worlds are reused; no heap/address relation is invented. -/
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

/-- Both branch choices execute real Source assignments, with distinct reached locals and transported target alignment, for both pipelines/check modes. -/
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

/-- A live condition write must be visible to the selected branch. Reading that branch from the initial state would return false instead of true. -/
theorem reached_effect_witness :
    (conditionalOperand (assignLocalOperand .here (.there .here))
      (assignLocalOperand (.there .here) .here) failing).run target =
      .ok (⟨(target.setLocal .here true).setLocal (.there .here) true,List.prefix_refl _⟩,.prim true) := by
  rw [conditionalOperand_run,assigned_condition_operand_run]
  rfl

/-- Each choice skips a failing unselected branch. Selecting that same branch, or failing the condition before selection, must propagate its halt. -/
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

private def literal (G : Source.Glob E) (F : Source.Fr) (b : Bool) :
    Condition G F mapping values worlds (.bool b) :=
  P12AtomicConditions.literal G F mapping values worlds b ⟨source,target,initial⟩

private def branchPanic (p : Roadmap.Pipeline) (checked side choose : Bool) :
    Condition (globals p) {F0 with checked := checked} mapping values worlds
      (.cond (.bool choose) (if side then V07.ShortCircuitControls.failure else .bool false)
        (if side then .bool false else V07.ShortCircuitControls.failure)) := by
  cases side
  · exact conditionalCondition (globals p) {F0 with checked := checked} mapping values worlds
      (.bool choose) (.bool false) V07.ShortCircuitControls.failure
      (literal _ _ choose) (literal _ _ false) (RevertControls.divisionCondition _ _)
  · exact conditionalCondition (globals p) {F0 with checked := checked} mapping values worlds
      (.bool choose) V07.ShortCircuitControls.failure (.bool false)
      (literal _ _ choose) (RevertControls.divisionCondition _ _) (literal _ _ false)

/-- The selected arm genuinely panics in Source, with exact transported native payload, for either arm and both pipelines/check modes. Rejects swallowed or reversed-arm panics; the existing producer's revert clause is exercised. -/
theorem taken_source_panic (p : Roadmap.Pipeline) (checked side : Bool) (fuel : Nat) :
    let expr : Source.RExpr E SrcCtx .bool :=
      .cond (.bool side) (if side then V07.ShortCircuitControls.failure else .bool false)
        (if side then .bool false else V07.ShortCircuitControls.failure)
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+7) expr).run source =
      (.error (.revert (Source.panicData .divZero)),source) ∧
    (branchPanic p checked side side).operand.run target =
      .error (THalt.ofData (Source.panicData .divZero)) := by
  dsimp only
  have run : (Source.evalE (globals p) {F0 with checked := checked} (fuel+7)
      (.cond (.bool side) (if side then V07.ShortCircuitControls.failure else .bool false)
        (if side then .bool false else V07.ShortCircuitControls.failure))).run source =
      (.error (.revert (Source.panicData .divZero)),source) := by
    rw [Source.evalE,Source.Hoare.run_bind,P12AtomicConditions.literal_source_run]
    dsimp only []
    rw [Source.Hoare.run_bind,source_getV_run]
    cases side
    all_goals
      dsimp only []
      simp only [Bool.false_eq_true,if_false,if_true]
      rw [RevertControls.division_source_run,if_pos (show 6 ≤ fuel+6 from by omega)]
  refine ⟨run,?_⟩
  cases side
  all_goals
    exact (branchPanic p checked _ _).revert (fuel+7) source source target
      (Source.panicData .divZero) initial run

/-- The same Source-panic arm is skipped even when its available horizon is insufficient. Guards against evaluating the unselected arm or returning panic unconditionally; both Source execution and native alignment are witnessed. -/
theorem skipped_source_panic (p : Roadmap.Pipeline) (checked side : Bool) (fuel : Nat) :
    let expr : Source.RExpr E SrcCtx .bool :=
      .cond (.bool (!side)) (if side then V07.ShortCircuitControls.failure else .bool false)
        (if side then .bool false else V07.ShortCircuitControls.failure)
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+2) expr).run source =
      (.ok (.val (.bool false)),source) ∧
    ∃ out : Out C target.H TgtCtx,
      (branchPanic p checked side (!side)).operand.run target = .ok (out,.prim false) ∧
      Aligned mapping values worlds source out.st := by
  dsimp only
  have run : (Source.evalE (globals p) {F0 with checked := checked} (fuel+2)
      (.cond (.bool (!side)) (if side then V07.ShortCircuitControls.failure else .bool false)
        (if side then .bool false else V07.ShortCircuitControls.failure))).run source =
      (.ok (.val (.bool false)),source) := by
    cases side <;> rfl
  refine ⟨run,?_⟩
  cases side
  all_goals
    exact (branchPanic p checked _ _).success (fuel+2) source source target false initial run

private def conditionPanic (p : Roadmap.Pipeline) (checked : Bool) :
    Condition (globals p) {F0 with checked := checked} mapping values worlds
      (.cond V07.ShortCircuitControls.failure (.bool true) (.bool false)) :=
  let G := globals p
  let F := {F0 with checked := checked}
  conditionalCondition G F mapping values worlds V07.ShortCircuitControls.failure
    (.bool true) (.bool false) (RevertControls.divisionCondition G F)
    (literal G F true) (literal G F false)

/-- A Source condition panic must propagate before either successful arm can run. Guards against treating condition failure as false or ignoring its data. -/
theorem condition_source_panic (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+7)
      (.cond V07.ShortCircuitControls.failure (.bool true) (.bool false))).run source =
      (.error (.revert (Source.panicData .divZero)),source) ∧
    (conditionPanic p checked).operand.run target =
      .error (THalt.ofData (Source.panicData .divZero)) := by
  have run : (Source.evalE (globals p) {F0 with checked := checked} (fuel+7)
      (.cond V07.ShortCircuitControls.failure (.bool true) (.bool false))).run source =
      (.error (.revert (Source.panicData .divZero)),source) := by
    rw [Source.evalE,Source.Hoare.run_bind,RevertControls.division_source_run,
      if_pos (show 6 ≤ fuel+6 from by omega)]
  exact ⟨run,(conditionPanic p checked).revert (fuel+7) source source target
    (Source.panicData .divZero) initial run⟩

#print axioms taken_source_panic
#print axioms skipped_source_panic
#print axioms condition_source_panic
#print axioms source_witness
#print axioms reached_effect_witness
#print axioms halt_selection
end Solidity.Lowering.G17.ConditionalControls
