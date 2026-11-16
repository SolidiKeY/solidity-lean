import Solidity.Yul.World.LifecycleFrames
import Solidity.Yul.World.SelfDestructControls
namespace Solidity.Yul.World.LifecycleFrameControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Yul.World.Checks Solidity.Yul.World.SelfDestructControls

def tagged := (freshEntry.recordCreation (addr 2)).recordCreation (addr 3)
def entry := (selfDestruct tagged false (addr 3) (addr 3)).get (by decide)
def first := (selfDestruct entry false (addr 1) (addr 2)).get (by decide)
def second := (selfDestruct first false (addr 2) (addr 2)).get (by decide)

theorem caller_prefix : entry.execution.journal.length = 3 ∧ entry.doomed (addr 3) = true ∧
    entry.doomed (addr 1) = false ∧ entry.doomed (addr 2) = false ∧
    (entry.execution.world.accounts (addr 1)).balance = toWord 100 ∧
    (entry.execution.world.accounts (addr 2)).balance = toWord 23 ∧
    (entry.execution.world.accounts (addr 3)).balance = toWord 0 := by
  decide

theorem actual_credit_then_burn : first.execution.journal.length = 5 ∧ second.execution.journal.length = 6 ∧
    (first.execution.world.accounts (addr 2)).balance = toWord 123 ∧
    (second.execution.world.accounts (addr 2)).balance = toWord 0 ∧
    second.doomed (addr 1) = true ∧ second.doomed (addr 2) = true := by
  decide

theorem full_rollback : rollbackLifecycle entry
    {second with execution := (first.execution.enter (addr 1) (addr 2) (toWord 999) [1,2] false).commit second.execution}
    (addr 1) (addr 2) (toWord 999) [1,2] false = entry := by
  exact rollbackLifecycle_two_committed entry first second false (addr 1) (addr 2) (addr 2) (addr 2)
    (Option.some_get _).symm (Option.some_get _).symm (addr 1) (addr 2) (toWord 999) [1,2] false
def rolled := rollbackLifecycle entry
    {second with execution := (first.execution.enter (addr 1) (addr 2) (toWord 999) [1,2] false).commit second.execution}
    (addr 1) (addr 2) (toWord 999) [1,2] false
theorem finalization_keeps_caller_prefix : (rolled.finish.execution.world.accounts (addr 1)).code = some 7 ∧
    (rolled.finish.execution.world.accounts (addr 2)).balance = toWord 23 ∧
    (rolled.finish.execution.world.accounts (addr 3)).code = none := by
  simp only [rolled,full_rollback]
  decide

def uncoupled := {second with execution :=
  (entry.execution.enter (addr 1) (addr 2) (toWord 999) [1,2] false).rollback second.execution}
theorem execution_only_leaks_deletion : (uncoupled.finish.execution.world.accounts (addr 1)).code = none ∧
    (rolled.finish.execution.world.accounts (addr 1)).code = some 7 := by
  simp only [rolled,full_rollback]
  decide
end Solidity.Yul.World.LifecycleFrameControls
