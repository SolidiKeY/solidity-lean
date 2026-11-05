import Solidity.Backend.AbiEntry.LengthCheck

/-! Exact boundary flags and actual semantic lazy/eager failure ordering.
These are not native allocation/panic certificates. -/
namespace Solidity.Backend.AbiEntry.LengthCheckControls
open Scalar
private def suffix : Stack := [258,513]
private def input : Solidity.AbiEntry.Input :=
  {data := List.replicate 23 0++[1]++List.replicate 8 0,free := 0}

private theorem load_zero : Solidity.AbiEntry.load input.data 0=2^64 := by decide
private theorem load_end : Solidity.AbiEntry.load input.data 32=0 := by decide

theorem boundaries :
    run LengthCheck.code (0::suffix)=some (1::suffix) ∧
    run LengthCheck.code (BitVec.ofNat 256 (2^64-1)::suffix)=some (1::suffix) ∧
    run LengthCheck.code (BitVec.ofNat 256 (2^64)::suffix)=some (0::suffix) ∧
    run LengthCheck.code (BitVec.ofNat 256 (2^256-1)::suffix)=some (0::suffix) := by decide

theorem raw_lazy_revert :
    Solidity.AbiEntry.tailRef input (.array (.word (.uint 256))) 0 32=.error .revert :=
  LengthCheck.lazy_revert input _ 0 32 (by rw [load_end]; decide) (by decide)
    (by rw [load_end]; change Solidity.AbiEntry.lim<Solidity.AbiEntry.load input.data 0
        rw [load_zero]; decide)

theorem raw_eager_array_panic (fuel allocated : Nat) :
    Solidity.AbiEntry.mdec input (fuel+1) (.array (.word (.uint 256))) 0 allocated=.error .panic :=
  LengthCheck.eager_array_panic input _ fuel 0 allocated (by decide) (by rw [load_zero]; decide)

theorem raw_eager_bytes_panic (fuel allocated : Nat) :
    Solidity.AbiEntry.mdec input (fuel+1) .bytes 0 allocated=.error .panic :=
  LengthCheck.eager_bytes_panic input fuel 0 allocated (by decide) (by rw [load_zero]; decide)

theorem short_before_panic (fuel allocated : Nat) :
    Solidity.AbiEntry.mdec input (fuel+1) .bytes 32 allocated=.error .revert := by
  simp only [Solidity.AbiEntry.mdec]
  rfl

theorem fuel_before_panic (allocated : Nat) :
    Solidity.AbiEntry.mdec input 0 .bytes 0 allocated=.error .fuel := rfl

theorem inhabited_frame :
    (LengthCheck.frameCertificate 0).peak=1 ∧
    run (LengthCheck.frameCertificate 0).code (0::suffix)=some (1::suffix) ∧
    stackBound LengthCheck.code 1024=false := ⟨rfl,boundaries.1,by decide⟩

/-- info: 'Solidity.Backend.AbiEntry.LengthCheckControls.boundaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- info: 'Solidity.Backend.AbiEntry.LengthCheckControls.raw_lazy_revert' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms raw_lazy_revert
/-- info: 'Solidity.Backend.AbiEntry.LengthCheckControls.raw_eager_array_panic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms raw_eager_array_panic
/-- info: 'Solidity.Backend.AbiEntry.LengthCheckControls.raw_eager_bytes_panic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms raw_eager_bytes_panic
/-- info: 'Solidity.Backend.AbiEntry.LengthCheckControls.short_before_panic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms short_before_panic
/-- info: 'Solidity.Backend.AbiEntry.LengthCheckControls.fuel_before_panic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fuel_before_panic
/-- info: 'Solidity.Backend.AbiEntry.LengthCheckControls.inhabited_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited_frame
end Solidity.Backend.AbiEntry.LengthCheckControls
