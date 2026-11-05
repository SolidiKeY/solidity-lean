import Solidity.Backend.AbiEntry.TailGuard

/-! Composite guards retain each failure and signed accepted offsets. Raw
semantic controls prove initial operand facts from bytes, not a decoded run. -/
namespace Solidity.Backend.AbiEntry.TailGuardControls
open Scalar
private def suffix : Stack := [258,513]
private def negative : Scalar.Word := BitVec.ofNat 256 (2^256-32)
private def wrappedAddress : Scalar.Word := BitVec.ofNat 256 (2^256-28)
private def input : Solidity.AbiEntry.Input := {data := List.replicate 32 0,free := 0}

theorem accepted : run TailGuard.code (32::68::4::32::0::32::68::36::suffix)=some (1::suffix) := by decide

theorem rejected_components :
    run TailGuard.code (32::68::4::33::0::32::68::36::suffix)=some (0::suffix) ∧
    run TailGuard.code (32::68::4::32::BitVec.ofNat 256 (2^64)::32::68::36::suffix)=some (0::suffix) ∧
    run TailGuard.code (32::68::4::32::2::32::68::36::suffix)=some (0::suffix) := by decide

theorem signed_accepted :
    run TailGuard.code (32::68::4::negative::0::32::68::wrappedAddress::suffix)=some (1::suffix) ∧
    68<negative.toNat := by decide

theorem raw_empty_array :
    Solidity.AbiEntry.tailRef input (.array (.word (.uint 256))) 0 0=.ok (32,0) := by
  have reference := TailGuard.reference input (.array (.word (.uint 256))) 0
    32 0 0 32 0 32 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  change Solidity.AbiEntry.tailRef input (.array (.word (.uint 256))) 0 0=
    if (Solidity.AbiEntry.tailFits 32 0 0 32 && decide ((0 : Nat)≤Solidity.AbiEntry.lim) &&
      Solidity.AbiEntry.regionFits 32 0 0 32)=true
    then .ok (Solidity.AbiEntry.wrap 32,0) else .error .revert at reference
  have pass : (Solidity.AbiEntry.tailFits 32 0 0 32 && decide ((0 : Nat)≤Solidity.AbiEntry.lim) &&
    Solidity.AbiEntry.regionFits 32 0 0 32)=true := by decide
  have address : Solidity.AbiEntry.wrap 32=32 := by decide
  rw [pass,if_pos rfl,address] at reference
  exact reference

theorem capacity_refused : stackBound TailGuard.code 1024=false := by decide

theorem inhabited_frame : (TailGuard.frameCertificate 68 4 32 32 0 32 36).peak=1 ∧
    run (TailGuard.frameCertificate 68 4 32 32 0 32 36).code
      (32::68::4::32::0::32::68::36::suffix)=some (1::suffix) := ⟨rfl,accepted⟩

/-- info: 'Solidity.Backend.AbiEntry.TailGuardControls.accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted
/-- info: 'Solidity.Backend.AbiEntry.TailGuardControls.rejected_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_components
/-- info: 'Solidity.Backend.AbiEntry.TailGuardControls.signed_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_accepted
/-- info: 'Solidity.Backend.AbiEntry.TailGuardControls.raw_empty_array' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms raw_empty_array
/-- info: 'Solidity.Backend.AbiEntry.TailGuardControls.capacity_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_refused
/-- info: 'Solidity.Backend.AbiEntry.TailGuardControls.inhabited_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited_frame
end Solidity.Backend.AbiEntry.TailGuardControls
