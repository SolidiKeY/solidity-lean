import Solidity.Yul.World.CallBuiltin
import Solidity.Yul.World.LifecycleAdapter
/-! Intrinsic SELFDESTRUCT binding to existing known-account lifecycle methods.
Outcome.success [] is the existing terminal tag, not an interpreter-exit proof.
Static/transfer refusal stays none. Environment credit, valid creation metadata,
reachable code/frame, physical/G01/G51/compiler/resource adequacy remain open. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Outcome)
variable {D : Layout} {L T : Address → Solidity.Source.SPath → STy}
/-- Known-account outcome-tagged leaf; actual interpreter exit remains external. -/
def selfDestructBuiltin {a : Nat} (builtin : Solidity.Yul.Builtin a 0)
    (entry : Lifecycle D L T) (frame : CallFrame) (args : Fin a → Word) :
    Option (Lifecycle D L T × Outcome) :=
  match builtin with
  | .selfdestruct => entry.destructAtFrame frame (calleeAddress (args 0))
  | _ => none

theorem selfDestructBuiltin_binding (entry : Lifecycle D L T) (frame : CallFrame) (args : Fin 1 → Word) :
    selfDestructBuiltin .selfdestruct entry frame args =
      entry.destructAtFrame frame (calleeAddress (args 0)) := by
  first | rfl | decide
theorem selfDestructBuiltin_static (entry : Lifecycle D L T) (frame : CallFrame) (args : Fin 1 → Word)
    (static : frame.static = true) :
    selfDestructBuiltin .selfdestruct entry frame args = none := by
  first | simp only [selfDestructBuiltin,destructAtFrame_static entry frame _ static] | decide | omega | rfl
theorem selfDestructBuiltin_success (entry : Lifecycle D L T) (frame : CallFrame) (args : Fin 1 → Word)
    (result : Lifecycle D L T × Outcome)
    (completed : selfDestructBuiltin .selfdestruct entry frame args = some result) :
    entry.destructKnown frame.static frame.this (calleeAddress (args 0)) = some result.1 ∧
      result.2 = .success [] := by
  exact destructTerminate_success entry frame.static frame.this (calleeAddress (args 0)) result completed
theorem selfDestructBuiltin_rollback (entry : Lifecycle D L T) (frame : CallFrame) (args : Fin 1 → Word)
    (result : Lifecycle D L T × Outcome)
    (completed : selfDestructBuiltin .selfdestruct entry frame args = some result)
    (receiver caller : Address) (value : Word) (input : Solidity.Roadmap.Bytes) (static : Bool) :
    entry.rollbackDestruction result.1 receiver caller value input static = entry := by
  exact destructKnown_rollback_all entry result.1 frame.static frame.this (calleeAddress (args 0))
    (selfDestructBuiltin_success entry frame args result completed).1 receiver caller value input static
theorem selfDestructBuiltin_other (entry : Lifecycle D L T) (frame : CallFrame) (args : Fin 1 → Word)
    (result : Lifecycle D L T × Outcome)
    (completed : selfDestructBuiltin .selfdestruct entry frame args = some result)
    (other : Address) (sourceOther : other ≠ frame.this) (beneficiaryOther : other ≠ calleeAddress (args 0)) :
    result.1.execution.world.accounts other = entry.execution.world.accounts other :=
  destructKnown_other entry result.1 frame.static frame.this (calleeAddress (args 0)) other
    (selfDestructBuiltin_success entry frame args result completed).1 sourceOther beneficiaryOther
end Solidity.Yul.World
