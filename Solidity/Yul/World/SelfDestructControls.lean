import Solidity.Yul.World.SelfDestruct
import Solidity.Yul.World.WorldChecks
namespace Solidity.Yul.World.SelfDestructControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Yul.World.Checks

def oldEntry : Lifecycle D₀ LW LW := ⟨fundedPrefix,fun _=>false,fun _=>false⟩
def freshEntry := oldEntry.recordCreation (addr 1)
def freshOut := (selfDestruct freshEntry false (addr 1) (addr 1)).get (by decide)
def paidOut := (selfDestruct oldEntry false (addr 1) (addr 2)).get (by decide)

theorem old_self_keeps_balance : (selfDestruct oldEntry false (addr 1) (addr 1)).map (fun out =>
    ((out.execution.world.accounts (addr 1)).balance, out.created (addr 1),out.doomed (addr 1))) =
      some (100,false,false) := by
  first | rfl | decide

theorem fresh_self_deferred : (freshOut.execution.world.accounts (addr 1)).balance = toWord 0 ∧
    (freshOut.execution.world.accounts (addr 1)).code = some 7 ∧
    (freshOut.execution.world.accounts (addr 1)).nonce = 3 ∧
    (freshOut.execution.world.accounts (addr 1)).storage.read countPath = some eight ∧
    freshOut.doomed (addr 1) = true ∧ freshOut.execution.journal.length = 3 := by
  first | decide | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem fresh_final_deleted : (freshOut.finish.execution.world.accounts (addr 1)).code = none ∧
    (freshOut.finish.execution.world.accounts (addr 1)).balance = toWord 0 ∧
    (freshOut.finish.execution.world.accounts (addr 1)).nonce = 0 := by
  first | decide | exact ⟨rfl,rfl,rfl⟩

theorem old_distinct_retained : (paidOut.execution.world.accounts (addr 1)).balance = toWord 0 ∧
    (paidOut.execution.world.accounts (addr 2)).balance = toWord 123 ∧
    (paidOut.finish.execution.world.accounts (addr 1)).code = some 7 ∧
    (paidOut.finish.execution.world.accounts (addr 1)).storage.read countPath = some eight := by
  first | decide | exact ⟨rfl,rfl,rfl,rfl⟩

theorem actual_burn_rollback : (fundedPrefix.enter (addr 1) (addr 2) (toWord 999) [1,2] false).rollback
    freshOut.execution = fundedPrefix := by
  exact selfDestruct_rollback freshEntry freshOut false (addr 1) (addr 1)
      (by simp only [freshOut,Option.some_get]) (addr 1) (addr 2) (toWord 999) [1,2] false

theorem static_refused : selfDestruct freshEntry true (addr 1) (addr 2) = none := by
  first | rfl | decide
def freshPaid := (selfDestruct freshEntry false (addr 1) (addr 2)).get (by decide)
theorem fresh_distinct_credit : (freshPaid.execution.world.accounts (addr 2)).balance = toWord 123 ∧
    (freshPaid.finish.execution.world.accounts (addr 1)).code = none ∧
    (freshPaid.finish.execution.world.accounts (addr 2)).balance = toWord 123 ∧
    (freshPaid.finish.execution.world.accounts (addr 3)).balance = toWord 41 := by
  first | decide | exact ⟨rfl,rfl,rfl,rfl⟩

def overflowEntry : Lifecycle D₀ LW LW :=
  {oldEntry with execution := {fundedPrefix with world := fundedPrefix.world.set (addr 2) {fundedPrefix.world.accounts (addr 2) with balance := 2^256-1}}}
theorem overflow_refused : selfDestruct overflowEntry false (addr 1) (addr 2) = none := by
  first | rfl | decide
end Solidity.Yul.World.SelfDestructControls
