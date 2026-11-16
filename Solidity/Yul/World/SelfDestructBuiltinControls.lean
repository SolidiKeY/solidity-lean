import Solidity.Yul.World.SelfDestructBuiltin
import Solidity.Yul.World.SelfDestructControls
namespace Solidity.Yul.World.SelfDestructBuiltinControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Yul.World.Checks Solidity.Yul.World.SelfDestructControls
open Solidity.Roadmap (Word)
/-- Typed context/metadata preparation, not deployed-code reachability. -/
def entry : Lifecycle D₀ LW LW := {oldEntry with execution := oldEntry.execution.apply (.account (addr 0x30) (fun account => {account with balance := toWord 17, nonce := 6, code := some 11}))}
def parent := entry.execution.enter (addr 1) (addr 2) (toWord 9) [0xaa] false
def delegated := childContext entry.execution parent .delegatecall (addr 0x30) (toWord 999) [17]
def args : Fin 1 → Word := fun _ => toWord (2^200+2)
def selfArgs : Fin 1 → Word := fun _ => toWord (2^200+1)
def oldResult := (selfDestructBuiltin .selfdestruct entry delegated args).get (by decide)
def fresh := entry.recordCreation (addr 1)
def freshResult := (selfDestructBuiltin .selfdestruct fresh delegated selfArgs).get (by decide)

theorem delegated_dirty_context : delegated.this = addr 1 ∧ delegated.caller = addr 2 ∧ delegated.value = toWord 9 ∧
    entry.execution.journal.length = 3 ∧ calleeAddress (args 0) = addr 2 ∧ (args 0).val ≠ 2 := by
  decide
theorem old_storage_owner_transfer : oldResult.2 = .success [] ∧
    (oldResult.1.execution.world.accounts (addr 1)).balance = toWord 0 ∧
    (oldResult.1.execution.world.accounts (addr 2)).balance = toWord 123 ∧
    (oldResult.1.execution.world.accounts (addr 0x30)).balance = toWord 17 ∧
    (oldResult.1.execution.world.accounts (addr 0x30)).code = some 11 ∧
    (oldResult.1.finish.execution.world.accounts (addr 1)).code = some 7 := by
  decide
theorem fresh_self_finalization : freshResult.2 = .success [] ∧
    (freshResult.1.execution.world.accounts (addr 1)).balance = toWord 0 ∧
    (freshResult.1.execution.world.accounts (addr 1)).code = some 7 ∧
    (freshResult.1.finish.execution.world.accounts (addr 1)).code = none ∧
    (freshResult.1.finish.execution.world.accounts (addr 1)).nonce = 0 := by
  decide
theorem static_refusal_isolated : selfDestructBuiltin .selfdestruct entry {delegated with static:=true} args = none ∧
    (selfDestructBuiltin .selfdestruct entry delegated args).isSome = true :=
  ⟨selfDestructBuiltin_static _ _ _ rfl,rfl⟩
theorem actual_result_rollback : entry.rollbackDestruction oldResult.1 delegated.this delegated.caller delegated.value
    delegated.input delegated.static = entry := by
  exact selfDestructBuiltin_rollback entry delegated args oldResult (Option.some_get (by decide)).symm
    delegated.this delegated.caller delegated.value delegated.input delegated.static
theorem complete_code_target_frame : oldResult.1.execution.world.accounts (addr 0x30) = entry.execution.world.accounts (addr 0x30) := by
  exact selfDestructBuiltin_other entry delegated args oldResult (Option.some_get (by decide)).symm
    (addr 0x30) (by decide) (by decide)
end Solidity.Yul.World.SelfDestructBuiltinControls
