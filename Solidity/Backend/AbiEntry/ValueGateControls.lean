import Solidity.Backend.AbiEntry.ValueGate

/-! Actual public compiler selection over an inhabited context and a machine
with distinct saved stack words and protected nonzero memory. These controls
observe the intrinsic target; no gas or byte-level revert claim is made. -/
namespace Solidity.Backend.AbiEntry.ValueGateControls
open Solidity.Evm
private def C : Contract := {vars := []}
private def Γ : Ctx := [.val .uint]
private def stage (payable : Bool) :
    Compiler.Compilation 7 (Frag.init Γ) (ValueGate.program (C := C) payable) :=
  ValueGate.compiled (C := C) 7 (Frag.init Γ) payable
private def machine (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value,stack := [.val (wmod 258),.val (wmod 513)],mem := fun _ => .val (wmod 71)}

theorem selected (payable : Bool) :
    Compiler.compile 7 (Frag.init Γ) (ValueGate.program (C := C) payable)=some (stage payable) :=
  ValueGate.selected _ _ _

theorem payable_any (value : Fin W) :
    run (stage true).code (machine value)=.ok (machine value) 0 :=
  ValueGate.executed _ _ _ _ (selected true) _

theorem zero_accepted : run (stage false).code (machine (wmod 0))=.ok (machine (wmod 0)) 0 :=
  ValueGate.executed _ _ _ _ (selected false) _

theorem nonzero_rejected (value : Fin W) (nonzero : value.val≠0) :
    run (stage false).code (machine value)=.revert := by
  have actual := ValueGate.executed _ _ _ _ (selected false) (machine value)
  change run (stage false).code (machine value)=
    (if false || decide (value.val=0) then .ok (machine value) 0 else .revert) at actual
  simpa only [Bool.false_or,decide_eq_false nonzero,Bool.false_eq_true,if_false] using actual

theorem maximum_rejected : run (stage false).code (machine (wmod (W-1)))=.revert :=
  nonzero_rejected _ (by decide)

theorem payable_nonzero_not_revert : run (stage true).code (machine (wmod 1))≠.revert := by
  rw [payable_any]
  intro impossible
  cases impossible

/-- info: 'Solidity.Backend.AbiEntry.ValueGateControls.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.ValueGateControls.payable_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_any
/-- info: 'Solidity.Backend.AbiEntry.ValueGateControls.zero_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_accepted
/-- info: 'Solidity.Backend.AbiEntry.ValueGateControls.nonzero_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonzero_rejected
/-- info: 'Solidity.Backend.AbiEntry.ValueGateControls.maximum_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maximum_rejected
/-- info: 'Solidity.Backend.AbiEntry.ValueGateControls.payable_nonzero_not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_nonzero_not_revert
end Solidity.Backend.AbiEntry.ValueGateControls
