import Solidity.Backend.AbiEntry.RawTailGuard

/-! Raw-byte guard cases, including a genuinely accepted signed relative offset
and unrestricted natural metadata. No supplied decoded payload or run. -/
namespace Solidity.Backend.AbiEntry.RawTailGuardControls
open Scalar Solidity.AbiEntry
private def suffix : Stack := [258,513]
private def array : Solidity.AbiEntry.Shape := .array (.word (.uint 256))
private def emptyArray : Input := {data := List.replicate 32 0,free := 0}
private def malformed : Input := {data := [],free := 0}
private def negativeInput : Input :=
  {data := [0,0,0,0]++wordBytes (2^256-32)++List.replicate 32 0,free := 0}
private theorem relative : load negativeInput.data 4=2^256-32 := by decide
private theorem wrapped : wrap (4+(2^256-32))=2^256-28 := by decide
private theorem length : load negativeInput.data (2^256-28)=0 := by decide

theorem empty_guard :
    run TailGuard.code (Interface.rawTailOperands emptyArray array 0 0++suffix)=some (1::suffix) := by
  rw [RawTailGuard.raw]
  have pass : Interface.rawTailCondition emptyArray array 0 0=true := by decide
  rw [pass]
  rfl

theorem malformed_guard :
    run TailGuard.code (Interface.rawTailOperands malformed array 0 0++suffix)=some (0::suffix) := by
  rw [RawTailGuard.raw]
  have fail : Interface.rawTailCondition malformed array 0 0=false := by decide
  rw [fail]
  rfl

theorem negative_condition : Interface.rawTailCondition negativeInput array 4 4=true := by
  dsimp only [Interface.rawTailCondition]
  rw [relative,wrapped,length]
  decide

theorem negative_guard :
    run TailGuard.code (Interface.rawTailOperands negativeInput array 4 4++suffix)=some (1::suffix) := by
  rw [RawTailGuard.raw,negative_condition]
  rfl

theorem negative_reference : tailRef negativeInput array 4 4=.ok (4,0) := by
  rw [RawTailGuard.reference negativeInput array 4 4 (by decide),negative_condition,if_pos rfl,
    relative,wrapped,length]
  have address : wrap ((2^256-28)+32)=4 := by decide
  rw [address]

private def huge : Solidity.AbiEntry.Shape := .array (.fixed (.word (.uint 256)) (2^256))

theorem huge_metadata :
    2^256≤huge.stride ∧
    run TailGuard.code (Interface.rawTailOperands emptyArray huge 0 0++suffix)=some (1::suffix) := by
  refine ⟨by decide,?_⟩
  rw [RawTailGuard.raw]
  have pass : Interface.rawTailCondition emptyArray huge 0 0=true := by decide
  rw [pass]
  rfl

/-- info: 'Solidity.Backend.AbiEntry.RawTailGuardControls.empty_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_guard
/-- info: 'Solidity.Backend.AbiEntry.RawTailGuardControls.malformed_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_guard
/-- info: 'Solidity.Backend.AbiEntry.RawTailGuardControls.negative_condition' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms negative_condition
/-- info: 'Solidity.Backend.AbiEntry.RawTailGuardControls.negative_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negative_guard
/-- info: 'Solidity.Backend.AbiEntry.RawTailGuardControls.negative_reference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms negative_reference
/-- info: 'Solidity.Backend.AbiEntry.RawTailGuardControls.huge_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms huge_metadata
end Solidity.Backend.AbiEntry.RawTailGuardControls
