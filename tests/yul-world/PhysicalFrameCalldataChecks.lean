import Solidity.Yul.World.PhysicalCall

/-! Actual producer-frame calldata and full-carrier read controls. These are
reads through an already-formed calldata reference, not reference formation,
callee admission, Yul calldata zero padding or a reachability certificate. -/
namespace Solidity.Yul.World.PhysicalFrameCalldataChecks
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

/-- Actual source bytesOfRV retains the entire physical carrier and observer. -/
theorem full_carrier_read {E Γ} (c : Carrier E Γ)
    (o : ObservedEffects E.layout E.lay E.lay) (frame : CallFrame)
    (contract : String) (checked : Bool) (depth horizon off len : Nat) :
    (let run := (Source.bytesOfRV (PhysicalSlotPort.sourceFrame frame contract checked depth)
       horizon (τ:=.bytes .calldata) (.val (.cdRef rfl off len))).run c.1.1
     ((run.1, (⟨⟨run.2,c.1.2⟩,c.2⟩ : Carrier E Γ)),o)) =
    ((.ok ((frame.input.drop off).take len),c),o) := by
  rfl

/-- Code target does not replace caller storage, sender or value; the actual
new call input is retained even when it differs from the parent input. -/
theorem delegate_frame {E Γ} (c : Carrier E Γ) (parent : CallFrame)
    (target : Address) (value : Word) (contract : String) (checked : Bool) (depth : Nat) :
    (let frame := PhysicalSlotPort.sourceFrame
      (enter c.1.1 c.1.2 parent .delegatecall target value [17,34,51,68]).source contract checked depth
     (frame.this,frame.sender,frame.value,frame.static,frame.cd)) =
    (parent.this,parent.caller,parent.value,parent.static,[17,34,51,68]) := by
  rfl

/-- Distinct interior bytes through the actual delegated physical frame. -/
theorem delegate_read {E Γ} (c : Carrier E Γ) (parent : CallFrame)
    (target : Address) (value : Word) (contract : String) (depth : Nat) :
    ((Source.bytesOfRV (PhysicalSlotPort.sourceFrame
      (enter c.1.1 c.1.2 parent .delegatecall target value [17,34,51,68]).source contract true depth)
      0 (τ:=.bytes .calldata) (.val (.cdRef rfl 1 2))).run c.1.1).1 = .ok [34,51] := by
  rfl

/-- An old empty calldata buffer cannot produce the selected interior bytes. -/
theorem stale_buffer {E Γ} (c : Carrier E Γ) (parent : CallFrame)
    (target : Address) (value : Word) (contract : String) (depth : Nat) :
    ((Source.bytesOfRV (PhysicalSlotPort.sourceFrame
      (enter c.1.1 c.1.2 parent .delegatecall target value []).source contract true depth)
      0 (τ:=.bytes .calldata) (.val (.cdRef rfl 1 2))).run c.1.1).1 ≠ .ok [34,51] := by
  change (Except.ok ([] : Bytes) : Except Halt Bytes) ≠ .ok [34,51]
  intro h
  cases h

#print axioms full_carrier_read
#print axioms delegate_frame
#print axioms delegate_read
#print axioms stale_buffer
#print axioms PhysicalCompletion.finish_revert_source
end Solidity.Yul.World.PhysicalFrameCalldataChecks
