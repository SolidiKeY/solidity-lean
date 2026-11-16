import Solidity.Lowering.G17.ShortCircuitSource
import Solidity.Lowering.V07.P12AtomicConditions
import Solidity.Lowering.V07.P12AssignedConditionControls

/-! Nonvacuity and negative controls for lazy composition. The inhabited fixture retains heterogeneous locals, memory and storage references. These controls reject eager RHS effects and incorrectly ignored taken-branch halts. -/
namespace Solidity.Lowering.G17.Controls
open V07 V07.P12NextInterface Source.SemanticsExamples
open V07.P12Controls (C E SrcCtx TgtCtx source target mapping)
open V07.P12AssignedConditionControls (values worlds initial bool_reflect)
open V07.MixedAssignmentControls (globals)

private def assignment : Source.RExpr E SrcCtx .bool :=
  .assign (.local .here) (.local (.there .here))

def skipped (conj : Bool) : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  shortOperand conj (P12AtomicConditions.literalOperand (!conj))
    (assignLocalOperand .here (.there .here))

/-- Guards against executing the RHS or losing the left result when skipped. -/
theorem skipped_run (conj : Bool) :
    (skipped conj).run target = .ok (⟨target,List.prefix_refl _⟩,.prim (!conj)) := by
  unfold skipped
  rw [shortOperand_run,P12AtomicConditions.literal_native_run]
  cases conj <;> rfl

/-- Eager RHS execution changes a live caller slot; it is observably different for both operators, even when its result equals the short-circuit result. -/
theorem eager_effect_rejected (conj : Bool) :
    (skipped conj).run target ≠ (assignLocalOperand .here (.there .here)).run target := by
  intro same
  rw [skipped_run,assigned_condition_operand_run] at same
  have observed := congrArg (fun result : TRes (Out C target.H TgtCtx × SVal (.prim .bool)) =>
    match result with | .ok (out,_) => TEnv.get .here out.st.env | .error _ => false) same
  cases observed

private def failing : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons .revert .nil,.val (.simple (.bool false))⟩

/-- A failing RHS must be skipped on one branch and propagated on the other. -/
theorem halt_control (conj : Bool) :
    (shortOperand conj (P12AtomicConditions.literalOperand (!conj)) failing).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (!conj)) ∧
    (shortOperand conj (P12AtomicConditions.literalOperand conj) failing).run target = .error .revert := by
  constructor
  all_goals
    rw [shortOperand_run,P12AtomicConditions.literal_native_run]
    cases conj <;> rfl

/-- Concrete input producers for the generic Source relation, with a real inhabited alignment rather than an assumed whole-expression execution law. -/
def producer (p : Roadmap.Pipeline) (checked conj : Bool) :=
  shortCondition (globals p) {F0 with checked := checked} mapping values worlds conj
    (.bool (!conj)) assignment
    (P12AtomicConditions.literal (globals p) {F0 with checked := checked} mapping values worlds
      (!conj) ⟨source,target,initial⟩)
    (P12AssignedConditionControls.producer p checked)

/-- Kernel-checked successful Source execution and its transported target execution, for both pipelines, both checking modes and both operators. -/
theorem source_witness (p : Roadmap.Pipeline) (checked conj : Bool) (fuel : Nat) :
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+2)
      (.binary (if conj then .and else .or) (.bool (!conj)) assignment)).run source =
        (.ok (.val (.bool (!conj))),source) ∧
    ∃ out : Out C target.H TgtCtx, (producer p checked conj).operand.run target =
      .ok (out,.prim (!conj)) ∧ Aligned mapping values worlds source out.st := by
  have sourceRun : (Source.evalE (globals p) {F0 with checked := checked} (fuel+2)
      (.binary (if conj then .and else .or) (.bool (!conj)) assignment)).run source =
        (.ok (.val (.bool (!conj))),source) := by
    cases conj <;> rfl
  exact ⟨sourceRun,(producer p checked conj).success (fuel+2) source source target (!conj) initial sourceRun⟩

private def reverseAssignment : Source.RExpr E SrcCtx .bool :=
  .assign (.local (.there .here)) (.local .here)

def takenProducer (p : Roadmap.Pipeline) (checked : Bool) :=
  shortCondition (globals p) {F0 with checked := checked} mapping values worlds true
    assignment reverseAssignment (P12AssignedConditionControls.producer p checked)
    (P12AssignedCondition.assignment (globals p) {F0 with checked := checked} mapping values worlds
      bool_reflect ⟨source,target,initial⟩ (.there .here) .here (.there .here) .here rfl rfl)

/-- The taken RHS reads the value written by the left assignment. This guards against reading the RHS from the initial state or dropping caller writes. -/
theorem taken_source_witness (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :
    let after : Source.EMState E SrcCtx :=
      ((source.1.set .here (.bool true)).set (.there .here) (.bool true),source.2)
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+3)
      (.binary .and assignment reverseAssignment)).run source = (.ok (.val (.bool true)),after) ∧
    ∃ out : Out C target.H TgtCtx, (takenProducer p checked).operand.run target =
      .ok (out,.prim true) ∧ Aligned mapping values worlds after out.st := by
  dsimp only
  have sourceRun : (Source.evalE (globals p) {F0 with checked := checked} (fuel+3)
      (.binary .and assignment reverseAssignment)).run source =
      (.ok (.val (.bool true)),
        ((source.1.set .here (.bool true)).set (.there .here) (.bool true),source.2)) := by
    simpa only [needsRight,if_true,Source.Idx.toNat] using
      (V07.source_short_assign_run (globals p) {F0 with checked := checked} fuel source true
        .here (.there .here) (.there .here) .here true false rfl rfl)
  exact ⟨sourceRun,(takenProducer p checked).success (fuel+3) source _ target true initial sourceRun⟩

#print axioms skipped_run
#print axioms eager_effect_rejected
#print axioms halt_control
#print axioms source_witness
#print axioms taken_source_witness

end Solidity.Lowering.G17.Controls
