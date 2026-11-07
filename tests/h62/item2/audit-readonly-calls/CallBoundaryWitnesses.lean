import Solidity.Backend.Passes.SourceCallBoundary

/-! Guard static writes being accepted, short return buffers being decoded, and
callee revert bytes being erased. Each original interface is applied to the
same explicit inputs as its observable run. These are Source boundary witnesses,
not compiled callee execution, gas/fork coverage or physical-frame adequacy. -/
namespace Solidity.H62.ReadonlyAudit.CallBoundaryWitnesses
open Solidity.Source
open Solidity.Backend.Passes.SourceCallBoundary

def environment : Env := ⟨[]⟩
def address : Solidity.Roadmap.Address := ⟨0, by decide⟩
def frame : Fr := { this := address, sender := address, value := ⟨0, by decide⟩, static := true, contract := "" }
def state : St environment :=
  { ex := { world := ⟨fun a => Account.empty (D := environment.layout) (environment.lay a)⟩,
            transient := ⟨fun _ => Storage.empty⟩, journal := [] }
    heap := Heap.empty, events := [], logs := [], fnLocals := ⟨[], .nil⟩ }
def operation : Op environment.layout environment.lay environment.lay :=
  .account address (fun account => account.withBalance 1)
def shortData : Solidity.Roadmap.Bytes := List.replicate 31 0

theorem static_joint : frame.static = true ∧
    applyOp (Γ := []) frame operation = (EM.halt (.revert []) : EM environment [] Unit) :=
  ⟨rfl, static_operation frame operation rfl⟩

theorem short_joint : shortData.length < 32 * ([STy.bool] : List STy).length ∧
    extReturn (E := environment) (Γ := []) [.bool] (.success shortData) = EM.halt (.revert []) :=
  ⟨by decide, return_short [.bool] shortData (by decide)⟩

theorem revert_joint :
    extReturn (E := environment) (Γ := []) [.bool] (.revert [7, 9]) = EM.halt (.revert [7, 9]) :=
  return_revert [.bool] [7, 9]

theorem static_observed :
    (applyOp (Γ := []) frame operation).run (.nil, state) =
      (.error (.revert []), (.nil, state)) := by
  rw [static_joint.2]
  rfl

theorem short_observed :
    (extReturn (E := environment) (Γ := []) [.bool] (.success shortData)).run (.nil, state) =
      (.error (.revert []), (.nil, state)) := by
  rw [short_joint.2]
  rfl

theorem revert_observed :
    (extReturn (E := environment) (Γ := []) [.bool] (.revert [7, 9])).run (.nil, state) =
      (.error (.revert [7, 9]), (.nil, state)) := by
  rw [revert_joint]
  rfl

/-- A static operation cannot be replaced by successful acceptance. -/
theorem static_acceptance_refused :
    applyOp (Γ := []) frame operation ≠ (pure () : EM environment [] Unit) := by
  intro same
  rw [static_joint.2] at same
  have observed : (Except.error (.revert []) : Except Halt Unit) = .ok () :=
    congrArg (fun action : EM environment [] Unit => (action.run (.nil, state)).1) same
  cases observed

/-- Replacing the callee's actual nonempty failure bytes by [] is detected. -/
theorem erased_revert_refused :
    extReturn (E := environment) (Γ := []) [.bool] (.revert [7, 9]) ≠ EM.halt (.revert []) := by
  intro same
  rw [revert_joint] at same
  have observed : (Except.error (.revert [7, 9]) : Except Halt (RVal environment.layout (STy.ret [.bool]))) = .error (.revert []) :=
    congrArg (fun action : EM environment [] (RVal environment.layout (STy.ret [.bool])) =>
      (action.run (.nil, state)).1) same
  cases observed

end Solidity.H62.ReadonlyAudit.CallBoundaryWitnesses
