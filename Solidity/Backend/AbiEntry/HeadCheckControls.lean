import Solidity.Backend.AbiEntry.HeadCheck

/-! Numeric predicate boundaries, actual early semantic failure ordering and
non-admission after a passed head. Huge heads are metadata, not an allocated
calldata buffer. Height refusal is a stack-bound observation, not native gas. -/
namespace Solidity.Backend.AbiEntry.HeadCheckControls
open Scalar
private def one : List Solidity.AbiEntry.Param := [{shape := .word .bool,loc := .value}]
private def mixed : List Solidity.AbiEntry.Param :=
  [{shape := .tuple [.fixed (.word (.uint 8)) 2,.word .bool],loc := .memory},
   {shape := .array (.word (.uint 256)),loc := .calldata}]
private def huge : List Solidity.AbiEntry.Param :=
  [{shape := .fixed (.word (.uint 256)) (2^256),loc := .memory}]
private def tail : Stack := [258,513]

theorem empty_signature_boundary :
    run (HeadCheck.code []) (3::tail)=some (1::tail) ∧
    run (HeadCheck.code []) (4::tail)=some (0::tail) := by decide

theorem one_word_boundary :
    run (HeadCheck.code one) (35::tail)=some (1::tail) ∧
    run (HeadCheck.code one) (36::tail)=some (0::tail) := by decide

theorem mixed_boundary : HeadCheck.need mixed=132 ∧
    run (HeadCheck.code mixed) (131::tail)=some (1::tail) ∧
    run (HeadCheck.code mixed) (132::tail)=some (0::tail) := by decide

theorem huge_is_short (size : Scalar.Word) :
    run (HeadCheck.code huge) (size::tail)=some (flag true::tail) := by
  have bound : 2^256≤HeadCheck.need huge := by decide
  have short : size.toNat<HeadCheck.need huge := Nat.lt_of_lt_of_le size.isLt bound
  have actual : run (HeadCheck.code huge) (size::tail)=
      some (flag (decide (size.toNat<HeadCheck.need huge))::tail) := HeadCheck.correct _ _ _
  simpa only [decide_eq_true short] using actual

theorem short_before_fuel :
    Solidity.AbiEntry.entry {data := [],free := 0} 0 one=.error .revert :=
  HeadCheck.early_revert _ _ _ (by decide)

theorem empty_head_no_fuel :
    Solidity.AbiEntry.entry {data := [0,0,0,0],free := 0} 0 []=.ok .nil := by rfl

private def dirty : Solidity.AbiEntry.Input :=
  {data := List.replicate 35 0++[2],free := 0}

theorem passed_head_not_entry :
    run (HeadCheck.code one) (36::tail)=some (0::tail) ∧
    Solidity.AbiEntry.entry dirty 2 one=.error .revert := by
  exact ⟨one_word_boundary.2,rfl⟩

theorem height_refusal : stackBound (HeadCheck.code one) 1024=false := by decide

theorem inhabited_frame :
    (HeadCheck.frameCertificate mixed (131 : Scalar.Word)).peak=1 ∧
    run (HeadCheck.frameCertificate mixed (131 : Scalar.Word)).code (131::tail)=some (1::tail) :=
  ⟨rfl,mixed_boundary.2.1⟩

/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.empty_signature_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_signature_boundary
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.one_word_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms one_word_boundary
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.mixed_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_boundary
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.huge_is_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms huge_is_short
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.short_before_fuel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_fuel
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.empty_head_no_fuel' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms empty_head_no_fuel
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.passed_head_not_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms passed_head_not_entry
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.height_refusal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms height_refusal
/-- info: 'Solidity.Backend.AbiEntry.HeadCheckControls.inhabited_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited_frame
end Solidity.Backend.AbiEntry.HeadCheckControls
