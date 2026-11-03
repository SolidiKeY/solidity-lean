import Solidity.Yul.World.LifecycleAdapter
import Solidity.Yul.World.WorldChecks

/-! Actual known-account destruction consumer controls; source/foreign-world
reachability and physical deletion agreement remain distinct obligations. -/
namespace Solidity.Yul.World.LifecycleAdapterChecks
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Yul.World.Checks
open Solidity.Roadmap (Outcome)

def burned : Lifecycle D₀ LW LW :=
  ⟨selfBeneficiary fundedPrefix true (addr 2), unscheduledLife.created,
    fun a => if a = addr 2 then true else false⟩

theorem burn_actual : unscheduledLife.destructKnown false (addr 2) (addr 2) = some burned := by
  rw [destructKnown_exact unscheduledLife (selfBeneficiary fundedPrefix true (addr 2))
    (addr 2) (addr 2) (by rfl)]
  simp only [Lifecycle.schedule, Bool.false_eq_true, ↓reduceIte, burned]
  congr 2
  funext other
  by_cases h : other = addr 2
  · subst other
    rfl
  · simp only [h, ↓reduceIte, unscheduledLife]

theorem burn_then_finish :
    (burned.execution.world.accounts (addr 2)).balance = toWord 0 ∧
    (burned.execution.world.accounts (addr 2)).code = some 8 ∧
    (burned.execution.world.accounts (addr 2)).nonce = 1 ∧
    (burned.execution.world.accounts (addr 2)).storage.read countPath = some eight ∧
    burned.finish.execution.world.accounts (addr 2) = Account.empty (LW (addr 2)) ∧
    (burned.finish.execution.world.accounts (addr 1)).balance = toWord 100 := by
  exact ⟨rfl, rfl, rfl, rfl, destructKnown_fresh_finish _ _ _ _ _ burn_actual (by decide), rfl⟩

/-- Full actual returned state rollback keeps the existing two-entry journal. -/
theorem burn_rollback :
    fundedPrefix.journal.length = 2 ∧
    unscheduledLife.rollbackDestruction burned (addr 2) (addr 1) (toWord 23) [17] false = unscheduledLife :=
  ⟨rfl, destructKnown_rollback_all _ _ _ _ _ burn_actual _ _ _ _ _⟩

/-- Old self-beneficiary balance survives, with nonempty code/nonce/storage. -/
theorem old_self_control :
    (unscheduledLife.destructTerminate false (addr 1) (addr 1)).map (fun p =>
      ((p.1.execution.world.accounts (addr 1)).balance,
       (p.1.execution.world.accounts (addr 1)).code,
       (p.1.execution.world.accounts (addr 1)).nonce,
       (p.1.execution.world.accounts (addr 1)).storage.read countPath,
       p.1.doomed (addr 1), p.2)) =
      some (toWord 100, some 7, 3, some eight, false, Outcome.success []) := rfl

/-- A fresh account pays a distinct funded known beneficiary, schedules only
itself, retains its code until finalization, then disappears. -/
theorem distinct_control :
    (unscheduledLife.destructKnown false (addr 2) (addr 1)).map (fun p =>
      ((p.execution.world.accounts (addr 2)).balance,
       (p.execution.world.accounts (addr 1)).balance,
       (p.execution.world.accounts (addr 3)).balance,
       p.doomed (addr 2), p.doomed (addr 1),
       (p.finish.execution.world.accounts (addr 2)).code,
       (p.finish.execution.world.accounts (addr 1)).code)) =
      some (toWord 0, toWord 123, toWord 41, true, false, none, some 7) := rfl

def oldPaid : Lifecycle D₀ LW LW :=
  ⟨paid, unscheduledLife.created, fun other =>
    if other = addr 1 then (unscheduledLife.doomed other || unscheduledLife.created other)
    else unscheduledLife.doomed other⟩

theorem old_paid_actual : unscheduledLife.destructKnown false (addr 1) (addr 2) = some oldPaid := rfl

/-- An old distinct source pays all its funds but keeps its complete remaining
record even after finalization; the fresh unscheduled beneficiary survives. -/
theorem old_distinct_control :
    (oldPaid.execution.world.accounts (addr 1)).balance = toWord 0 ∧
    (oldPaid.execution.world.accounts (addr 2)).balance = toWord 123 ∧
    (oldPaid.finish.execution.world.accounts (addr 1)).code = some 7 ∧
    (oldPaid.finish.execution.world.accounts (addr 1)).nonce = 3 ∧
    (oldPaid.finish.execution.world.accounts (addr 1)).storage.read countPath = some eight ∧
    (oldPaid.finish.execution.world.accounts (addr 2)).code = some 8 ∧
    unscheduledLife.rollbackDestruction oldPaid (addr 1) (addr 2) (toWord 100) [] false = unscheduledLife := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    destructKnown_rollback_all _ _ _ _ _ old_paid_actual _ _ _ _ _⟩

def afterChild : Lifecycle D₀ LW LW :=
  ⟨selfBeneficiary (fundedPrefix.run havoc) true (addr 2), unscheduledLife.created,
    fun other => if other = addr 2 then (unscheduledLife.doomed other || unscheduledLife.created other)
      else unscheduledLife.doomed other⟩

theorem child_actual :
    ({ unscheduledLife with execution := fundedPrefix.run havoc }).destructKnown false (addr 2) (addr 2) =
      some afterChild := rfl

theorem enclosing_destruction_rollback :
    unscheduledLife.rollbackDestruction { afterChild with execution := afterChild.execution.run callOps }
      (addr 1) (addr 2) (toWord 999) [42] false = unscheduledLife :=
  destructKnown_outer_rollback unscheduledLife afterChild havoc callOps false (addr 2) (addr 2)
    child_actual _ _ _ _ _

/-- Static rejection has no normal terminating result, rather than pretending
the callee returned a failure status; source exceptional rollback is separate. -/
theorem static_control :
    unscheduledLife.destructTerminate true (addr 2) (addr 1) = none := rfl

/-- Finalization resets transaction-local creation/deletion metadata; the old
survivor in a new transaction is not eligible for deferred deletion. -/
theorem reset_control :
    (unscheduledLife.finish.destructKnown false (addr 2) (addr 2)).map (fun p =>
      (p.created (addr 2), p.doomed (addr 2), (p.execution.world.accounts (addr 2)).balance,
       (p.finish.execution.world.accounts (addr 2)).code)) = some (false, false, toWord 23, some 8) := rfl

theorem destruction_negatives :
    (burned.execution.world.accounts (addr 2)).balance ≠ toWord 23 ∧
    (burned.finish.execution.world.accounts (addr 2)).code ≠ some 8 ∧
    (burned.finish.execution.world.accounts (addr 1)).balance ≠ toWord 0 := by decide

theorem termination_rule_control :
    ∀ result, unscheduledLife.destructTerminate false (addr 2) (addr 2) = some result →
      result = (burned, Outcome.success []) := destruct_termination_rule _ _ _ _ _ burn_actual

theorem wrong_termination_refused :
    unscheduledLife.destructTerminate false (addr 2) (addr 2) ≠ some (burned, Outcome.revert []) := by
  intro h
  have ho := (destructTerminate_success _ _ _ _ _ h).2
  cases ho

def parent : CallFrame := fundedPrefix.enter (addr 1) (addr 42) (toWord 99) [] false

def delegated : CallFrame := childContext fundedPrefix parent .delegatecall (addr 2) (toWord 0) [17]

/-- Library code address 2 is fresh, but delegated SELFDESTRUCT targets old
caller address 1. The library's balance/code are not scheduled or destroyed. -/
theorem delegated_destruction :
    (unscheduledLife.destructAtFrame delegated (addr 3)).map (fun p =>
      ((p.1.execution.world.accounts (addr 1)).balance,
       (p.1.execution.world.accounts (addr 2)).balance,
       (p.1.execution.world.accounts (addr 3)).balance,
       p.1.doomed (addr 1), p.1.doomed (addr 2),
       (p.1.finish.execution.world.accounts (addr 1)).code,
       (p.1.finish.execution.world.accounts (addr 2)).code, p.2)) =
      some (toWord 0, toWord 23, toWord 141, false, false, some 7, some 8, Outcome.success []) := rfl

theorem nested_static_destruction :
    let frame := childContext fundedPrefix { parent with static := true } .delegatecall (addr 2) (toWord 0) [17]
    unscheduledLife.destructAtFrame frame (addr 3) = none := rfl

#print axioms burn_actual
#print axioms burn_rollback
#print axioms distinct_control
end Solidity.Yul.World.LifecycleAdapterChecks
