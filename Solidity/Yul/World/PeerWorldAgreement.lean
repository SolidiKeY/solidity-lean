import Solidity.Backend.AbiWorld.WorldFrames
import Solidity.Yul.World.Adapters
import Solidity.Yul.World.WorldChecks

/-! Actual V13 66c08fde WorldFrames composition, not source/callee adequacy. -/
namespace Solidity.Yul.World.PeerWorldAgreement
open Solidity.Source
open Solidity.Roadmap (Address)
variable {D : Solidity.Source.Layout} {L T : Address → Solidity.Source.SPath → Solidity.Source.STy}

/-- Every unrelated persistent AND transient account observation is preserved
by actual consumer completion, on either callee success or rollback. -/
theorem completion_unrelated (entry : ObservedEffects D L T) (frame : CallFrame)
    (answer : FrameAnswer D L T) (a : Address)
    (separated : ∀ op ∈ answer.operations, Solidity.Backend.AbiWorld.operationOwner op ≠ a) :
    (((finishObserved entry frame answer).effects.execution.world.accounts a),
      ((finishObserved entry frame answer).effects.execution.transient.cells a)) =
      (entry.effects.execution.world.accounts a, entry.effects.execution.transient.cells a) := by
  cases answer with
  | mk ops trace outcome =>
    cases outcome with
    | success data => exact Solidity.Backend.AbiWorld.unrelated_world_frame _ _ _ separated
    | revert data =>
      rw [(finishObserved_revert entry frame ops trace data).1]

/-- The actual inherited CALL/STATICCALL/DELEGATECALL frame has the entry mark,
regardless of its heterogeneous sender/storage/value fields. -/
theorem child_mark (entry : ExecState D L T) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (value : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes) :
    (childContext entry parent kind callee value input).mark = entry.journal.length := by
  cases kind <;> rfl

theorem actual_callback_rollback (entry : ExecState D L T) (prior inner : List (Op D L T))
    (parent : CallFrame) (kind : CallKind) (callee : Address)
    (value : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (outerMark : parent.mark = entry.journal.length) :
    (childContext (entry.run prior) parent kind callee value input).rollback
        ((entry.run prior).run inner) = entry.run prior ∧
    parent.rollback ((childContext (entry.run prior) parent kind callee value input).rollback
        ((entry.run prior).run inner)) = entry :=
  Solidity.Backend.AbiWorld.heterogeneous_callback_rollback entry prior inner parent
    (childContext (entry.run prior) parent kind callee value input) outerMark (child_mark _ _ _ _ _ _)

#print axioms completion_unrelated
#print axioms actual_callback_rollback
end Solidity.Yul.World.PeerWorldAgreement
