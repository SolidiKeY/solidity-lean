import Solidity.Lowering.G16.Complement
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.AliasRhsSubtraction

/-! Inhabited mixed-location complement clients and width/sign controls. -/
namespace Solidity.Lowering.G16.ComplementControls
open Solidity.Lowering.V07

/-- Instantiate the actual transport with mixed local/memory/storage clients
for every width, sign, checked mode and pipeline. -/
def client (t : Source.IntTy) (checked : Bool) (x : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  Complement.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source t x 0 hx (integer_zero_range t))
    (WordCastControls.target t x 0 hx (integer_zero_range t)) t
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t x 0 hx (integer_zero_range t)) true x hx rfl

/-- Guards against forgetting unsigned width restoration and interpreting a
signed complement as the nonnegative word bit pattern. -/
theorem wrong_complement_rejected :
    Source.IntTy.u8.wrap (-0-1) ≠ -1 ∧
    (SignedWidthCasts.ty 8 (by decide)).wrap (-0-1) ≠ 255 := by
  decide

def unsigned_boundary (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client .u8 checked 0 (by decide) pipeline fuel

def signed_boundary (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client (SignedWidthCasts.ty 8 (by decide)) checked 0 (by decide) pipeline fuel

end Solidity.Lowering.G16.ComplementControls

/-- info: 'Solidity.Lowering.G16.ComplementControls.wrong_complement_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ComplementControls.wrong_complement_rejected

namespace Solidity.Lowering.G16.UnsignedBitwiseControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.UnsignedBitwise

/-- Inhabited mixed-location callers for every unsigned width, operator, frame and pipeline. -/
def width_client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  let t := UnsignedNarrowing.ty bits valid
  transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source t 0 0 (integer_zero_range t) (integer_zero_range t))
    (WordCastControls.target t 0 0 (integer_zero_range t) (integer_zero_range t))
    op bits valid .here (.there .here) .here (.there .here) 0 0
    (Nat.two_pow_pos bits) (Nat.two_pow_pos bits) rfl rfl rfl rfl

private def sampleSource := WordCastControls.source .u8 12 10 (by decide) (by decide)
private def sampleTarget := WordCastControls.target .u8 12 10 (by decide) (by decide)

private def sourceObserved (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Int :=
  match (Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+3)
    (.binary (sourceOp op) (.local .here) (.local (.there .here)))).run sampleSource |>.1 with
  | .ok (.val v) => v.key
  | _ => none

private def targetObserved (op : Op) : Option Int :=
  ((value op (.simple (.local .here)) (.simple (.local (.there .here)))).evalT sampleTarget).toOption.map (·.val)

private theorem sample_run (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    sourceObserved op checked pipeline fuel = some (result op 12 10 : Int) ∧
    targetObserved op = some (result op 12 10 : Int) := by
  have runs := transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel sampleSource sampleTarget
    op 8 (by decide) .here (.there .here) .here (.there .here) 12 10
    (by decide) (by decide) rfl rfl rfl rfl
  constructor
  · unfold sourceObserved
    rw [runs.1]
    rfl
  · unfold targetObserved
    rw [runs.2]
    rfl

/-- Reject replacing any bitwise opcode by addition; actual Source/native results also distinguish all three opcodes. -/
theorem wrong_bitwise_rejected (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    sourceObserved .and checked pipeline fuel = some 8 ∧
    sourceObserved .or checked pipeline fuel = some 14 ∧
    sourceObserved .xor checked pipeline fuel = some 6 ∧
    targetObserved .and = some 8 ∧ targetObserved .or = some 14 ∧ targetObserved .xor = some 6 ∧
    sourceObserved .and checked pipeline fuel ≠ some 22 ∧
    sourceObserved .or checked pipeline fuel ≠ some 22 ∧
    sourceObserved .xor checked pipeline fuel ≠ some 22 := by
  have andRun := sample_run .and checked pipeline fuel
  have orRun := sample_run .or checked pipeline fuel
  have xorRun := sample_run .xor checked pipeline fuel
  rw [andRun.1,orRun.1,xorRun.1,andRun.2,orRun.2,xorRun.2]
  decide

end Solidity.Lowering.G16.UnsignedBitwiseControls

/-- info: 'Solidity.Lowering.G16.UnsignedBitwiseControls.wrong_bitwise_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.UnsignedBitwiseControls.wrong_bitwise_rejected
