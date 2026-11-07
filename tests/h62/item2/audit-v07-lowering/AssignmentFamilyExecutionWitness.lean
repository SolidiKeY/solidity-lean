import tests.h62.item2.«audit-v07-lowering».IntegerLocalFamilyWitness
import Solidity.Lowering.V07.MixedAssignmentControls

/-!
Guarded regression: an inhabited local family must not be reported as completed
assignment execution without binding the actual Source run and target operand
to the same states. The two selected slots below retain all alias/value fields,
and the postfamily is derived. The target cannot reject every state. These are
local assignment results, not gas, whole-compiler totality or global alignment.
-/
namespace Solidity.H62.AuditV07.AssignmentFamilyExecutionWitness
open Solidity.Lowering.V07
open IntegerLocalFamilyWitness

def targetState {C : Contract} (base : State C []) (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :=
  (base.push (t := .val (integerPrim t)) (integerValue t y hy)).push
    (t := .val (integerPrim t)) (integerValue t x hx)

/-- Actual completion and family preservation share the same initial states. -/
theorem joint_execution {E : Source.Env} {C : Contract}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (world : Source.St E) (base : State C []) (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) (written rhs : Bool) :
    let source := (sourceLocals E.layout t x y hx hy, world)
    let target := targetState base t x y hx hy
    (Source.evalE G F (fuel+2)
      (.assign (.local (sourceIndex t written)) (.local (sourceIndex t rhs)))).run source =
      (.ok (.val (source.1.get (sourceIndex t rhs))),
        (source.1.set (sourceIndex t written) (source.1.get (sourceIndex t rhs)),world)) ∧
    (assignLocalOperand (targetIndex t written) (targetIndex t rhs)).run target =
      .ok (⟨target.setLocal (targetIndex t written)
        (TEnv.get (targetIndex t rhs) target.env),List.prefix_refl _⟩,
        .prim (TEnv.get (targetIndex t rhs) target.env)) ∧
    IntegerLocalFamily t (sourceIndex t) (targetIndex t)
      (source.1.set (sourceIndex t written) (source.1.get (sourceIndex t rhs)))
      (target.setLocal (targetIndex t written) (TEnv.get (targetIndex t rhs) target.env)).env :=
  assignment_family_transport t (sourceIndex t) (targetIndex t) G F fuel
    (sourceLocals E.layout t x y hx hy, world) (targetState base t x y hx hy)
    (related_family E.layout C base.H t x y hx hy) written rhs

/-- Every local operand in this two-slot family has a successful initial state. -/
theorem cannot_reject_all {C : Contract} (base : State C []) (t : Source.IntTy)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (written rhs : Bool) (reason : THalt) :
    ¬ (∀ reached : State C [.val (integerPrim t), .val (integerPrim t)],
      (assignLocalOperand (targetIndex t written) (targetIndex t rhs)).run reached =
        .error reason) := by
  intro rejects
  have success := assign_local_operand_run (targetState base t x y hx hy)
    (targetIndex t written) (targetIndex t rhs) _ rfl
  rw [rejects] at success
  cases success

/-- A concrete existing Source world and target base inhabit the shared inputs. -/
theorem initial_family_inhabited :
    ∃ (E : Source.Env) (C : Contract) (G : Source.Glob E) (F : Source.Fr)
      (world : Source.St E) (base : State C []) (t : Source.IntTy) (x y : Int)
      (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi),
      IntegerLocalFamily t (sourceIndex t) (targetIndex t)
        (sourceLocals E.layout t x y hx hy) (targetState base t x y hx hy).env := by
  let hx : Source.IntTy.u8.lo ≤ 7 ∧ 7 ≤ Source.IntTy.u8.hi := by decide
  let hy : Source.IntTy.u8.lo ≤ 9 ∧ 9 ≤ Source.IntTy.u8.hi := by decide
  exact ⟨MixedAssignmentControls.E, MixedAssignmentControls.C,
    MixedAssignmentControls.globals .viaIR, Source.SemanticsExamples.F0,
    MixedAssignmentControls.source.2, State.init MixedAssignmentControls.C,
    Source.IntTy.u8, 7, 9, hx, hy,
    related_family _ _ _ _ 7 9 hx hy⟩

#check @assignment_family_transport
#print axioms joint_execution
#print axioms cannot_reject_all
#print axioms initial_family_inhabited
end Solidity.H62.AuditV07.AssignmentFamilyExecutionWitness
