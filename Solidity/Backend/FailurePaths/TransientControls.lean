import Solidity.Backend.FailurePaths.TransientUnwind
import Solidity.Backend.FailurePaths.Premises
import Solidity.Roadmap.Controls

/-!
# G38/P7 inhabited empty-failure and nonempty-refusal controls

P7's source and target prefixes are deliberately nonempty. The target is its
published numeric transient adapter, not the complete EVM evaluator.
-/
namespace Solidity.Backend.FailurePaths.TransientControls
open Source Transient.Controls

def program : Source.Program env where
  body := fun _ => none
  consts := fun _ => none
  inits := fun _ => []
  ctor := fun _ => none
  ctorLocals := fun _ => []
  baseArgs := fun _ => []
  contracts := ["P7"]

def global (pipeline : Roadmap.Pipeline) : Glob env where
  prog := program
  pipeline := pipeline
  fixed := Roadmap.Controls.toyFixed
  balance0 := fun _ => ⟨100, by decide⟩
  hasCode := fun _ _ => false
  callee := fun _ => .answer (.success [])
  timestamp := ⟨0, by decide⟩

theorem empty_failure (pipeline : Roadmap.Pipeline) :
    (TransientUnwind.source (global pipeline) frame 0 slot true prefixedSource.1).run
      (Source.L0 env, prefixedSource.2) =
      (.error (.revert []), (Source.L0 env, Transient.sourceWrite slot owner true prefixedSource.2)) ∧
    Transient.callbackInFrame frame
      (Transient.storeCode slot.key (Transient.boolWord true) ++ Failure.emit 0 .empty) target =
      .error .reverted target := by
  have paired := TransientUnwind.paired_bare_failure (global pipeline) frame 0 slot rfl true
    prefixedSource.1 prefixedSource.2 target
  exact ⟨paired.2.1, paired.2.2.1⟩

theorem restored_source :
    {Transient.sourceWrite slot owner true prefixedSource.2 with ex := (
      (prefixedSource.2.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
        (Transient.sourceWrite slot owner true prefixedSource.2).ex)} = prefixedSource.2 :=
  TransientUnwind.source_restored frame slot true prefixedSource.2

/-- The initial and restored selected-cell relation is inhabited on P7's
nonempty caller prefixes; arbitrary target state pairing alone is insufficient. -/
theorem restored_relation (pipeline : Roadmap.Pipeline) :
    Transient.Represents slot owner (Source.L0 env,
      {Transient.sourceWrite slot owner true prefixedSource.2 with ex := (
        (prefixedSource.2.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
          (Transient.sourceWrite slot owner true prefixedSource.2).ex)}) target :=
  (TransientUnwind.simulates_bare_failure (global pipeline) frame 0 slot rfl true
    prefixedSource.1 prefixedSource.2 target initial_relation).2.2

/-- Expose the exact adapter class and dirty selected bank after unsupported
payload emission; this must not be mistaken for a completed reverting frame. -/
def nonemptyObservation : String × Bool :=
  match Transient.callbackInFrame frame
      (Transient.storeCode slot.key (Transient.boolWord true) ++ Failure.emit 0 (.custom [1])) target with
  | .error .unsupported dirty => ("unsupported", dirty.bank owner slot.key == Transient.boolWord true)
  | .error .reverted _ => ("reverted", false)
  | _ => ("other", false)

theorem nonempty_payload_refused : nonemptyObservation = ("unsupported", true) := by decide +kernel

def isReverted : Transient.Result → Bool
  | .error .reverted _ => true
  | _ => false

theorem payload_only_unsupported :
    isReverted (Transient.callbackInFrame frame (Failure.emit 0 (.custom [1])) target) = false := by
  decide +kernel

/-- The residual joint transport contract cannot be supplied for the current
nonempty emitter/P7 adapter, for ANY proposed byte machine or live-cell set. -/
theorem no_current_payload_transport (bytes : Failure.Slice.Machine) (cells : List Nat) :
    ¬ Premises.TransientPayloadAt frame (Failure.emit 0 (.custom [1])) target bytes cells 0 [1] := by
  intro transport
  have observed := congrArg isReverted transport.2.2
  rw [payload_only_unsupported] at observed
  cases observed

def sourceObservation (pipeline : Roadmap.Pipeline) : Option Roadmap.Bytes :=
  match (TransientUnwind.source (global pipeline) frame 0 slot true prefixedSource.1).run
      (Source.L0 env, prefixedSource.2) |>.1 with
  | .error (.revert bytes) => some bytes
  | _ => none

def targetObservation : String :=
  match Transient.callbackInFrame frame
      (Transient.storeCode slot.key (Transient.boolWord true) ++ Failure.emit 0 .empty) target with
  | .error .reverted _ => "empty revert"
  | _ => "other"

#eval sourceObservation .legacy
#eval sourceObservation .viaIR
#eval targetObservation
#eval nonemptyObservation
#print axioms empty_failure
#print axioms restored_source
#print axioms restored_relation
#print axioms nonempty_payload_refused
#print axioms no_current_payload_transport
end Solidity.Backend.FailurePaths.TransientControls
