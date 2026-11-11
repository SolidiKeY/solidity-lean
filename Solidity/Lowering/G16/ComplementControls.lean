import Solidity.Lowering.G16.Complement
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.AliasRhsSubtraction

/-! Inhabited mixed-location complement clients and width/sign controls. -/
namespace Solidity.Lowering.G16.ComplementControls
open Solidity.Lowering.V07

/-- Instantiate the actual transport with mixed local/memory/storage clients for every width, sign, checked mode and pipeline. -/
def client (t : Source.IntTy) (checked : Bool) (x : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  Complement.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source t x 0 hx (integer_zero_range t))
    (WordCastControls.target t x 0 hx (integer_zero_range t)) t
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t x 0 hx (integer_zero_range t)) true x hx rfl

/-- Guards against forgetting unsigned width restoration and interpreting a signed complement as the nonnegative word bit pattern. -/
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

namespace Solidity.Lowering.G16.UnsignedBitwiseControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.UnsignedBitwise

/-- Inhabited assignment/read callers at all unsigned widths, operators, modes and pipelines. -/
def assignment_width_client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  let t := UnsignedNarrowing.ty bits valid
  assignment_transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source t 0 0 (integer_zero_range t) (integer_zero_range t))
    (WordCastControls.target t 0 0 (integer_zero_range t) (integer_zero_range t))
    op bits valid (.there .here) .here (.there .here) .here 0 0
    (Nat.two_pow_pos bits) (Nat.two_pow_pos bits) rfl rfl rfl rfl

private def assignmentSource (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  (Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.binary (sourceOp op) (.assign (.local (.there .here)) (.local .here))
      (.local (.there .here)))).run sampleSource

private def assignmentObserved (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Int :=
  match (assignmentSource op checked pipeline fuel).1 with
  | .ok (.val v) => v.key
  | _ => none

private def sourceWritten (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Int :=
  ((assignmentSource op checked pipeline fuel).2.1.get (.there .here)).key

private def nativeObserved (op : Op) (pipeline : Roadmap.Pipeline) : Option Int :=
  match (assignmentOperand op pipeline (.there .here) .here).run sampleTarget with
  | .ok (_, .prim v) => some v.val
  | .error _ => none

private def nativeWritten (op : Op) (pipeline : Roadmap.Pipeline) : Option Int :=
  match (assignmentOperand op pipeline (.there .here) .here).run sampleTarget with
  | .ok (out,_) => some (TEnv.get (.there .here) out.st.env).val
  | .error _ => none

private theorem assignment_sample_run (op : Op) (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    assignmentObserved op checked pipeline fuel = some (result op 12 (captureRight pipeline 12 10) : Int) ∧
    nativeObserved op pipeline = some (result op 12 (captureRight pipeline 12 10) : Int) ∧
    sourceWritten op checked pipeline fuel = some 12 ∧ nativeWritten op pipeline = some 12 := by
  have runs := assignment_transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel sampleSource sampleTarget
    op 8 (by decide) (.there .here) .here (.there .here) .here 12 10
    (by decide) (by decide) rfl rfl rfl rfl
  have native := runs.2
  dsimp only [MixedAssignmentControls.globals] at native
  refine ⟨?_,?_,?_,?_⟩
  · unfold assignmentObserved assignmentSource
    rw [runs.1]
    rfl
  · unfold nativeObserved
    rw [native]
    rfl
  · unfold sourceWritten assignmentSource
    rw [runs.1,source_locals_get_set]
    rfl
  · unfold nativeWritten
    rw [native]
    change some (TEnv.get (.there .here) (TEnv.set (.there .here) _ sampleTarget.env)).val = some 12
    rw [TEnv.get_set]
    rfl

/-- Actual evaluations reject erased operand order for every opcode and dropped named writes in either mode/pipeline. -/
theorem wrong_assignment_bitwise_rejected (checked : Bool) (fuel : Nat) :
    assignmentObserved .and checked .legacy fuel ≠ assignmentObserved .and checked .viaIR fuel ∧
    assignmentObserved .or checked .legacy fuel ≠ assignmentObserved .or checked .viaIR fuel ∧
    assignmentObserved .xor checked .legacy fuel ≠ assignmentObserved .xor checked .viaIR fuel ∧
    (∀ op p, sourceWritten op checked p fuel = some 12 ∧ nativeWritten op p = some 12) ∧
    (∀ op p, nativeObserved op p = assignmentObserved op checked p fuel) := by
  have andLegacy := assignment_sample_run .and checked .legacy fuel
  have andIR := assignment_sample_run .and checked .viaIR fuel
  have orLegacy := assignment_sample_run .or checked .legacy fuel
  have orIR := assignment_sample_run .or checked .viaIR fuel
  have xorLegacy := assignment_sample_run .xor checked .legacy fuel
  have xorIR := assignment_sample_run .xor checked .viaIR fuel
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [andLegacy.1,andIR.1]
    decide
  · rw [orLegacy.1,orIR.1]
    decide
  · rw [xorLegacy.1,xorIR.1]
    decide
  · intro op p
    exact (assignment_sample_run op checked p fuel).2.2
  · intro op p
    rw [(assignment_sample_run op checked p fuel).1,(assignment_sample_run op checked p fuel).2.1]

/-- info: 'Solidity.Lowering.G16.UnsignedBitwiseControls.wrong_assignment_bitwise_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_assignment_bitwise_rejected
end UnsignedBitwiseControls

end Solidity.Lowering.G16

namespace Solidity.Lowering.G16.UnsignedShiftControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.UnsignedShifts

private theorem amount_range (n : Nat) (bound : n < 2^256) :
    Source.IntTy.u256.lo ≤ (n : Int) ∧ (n : Int) ≤ Source.IntTy.u256.hi := by
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ ((2^256-1 : Nat) : Int)
  have positive := Source.two_pow_pos 256
  omega

private def source (n : Nat) (bound : n < 2^256) :
    Source.EMState MixedAssignmentControls.E [.int .u8,.int .u256,.bytes .memory,.bytes .storage] :=
  (.cons (.int 129 (by decide)) (.cons (.int (n : Int) (amount_range n bound))
    (.cons (.memRef rfl 0) (.cons (.storRef rfl MixedAssignmentControls.path) .nil))),
    {Source.SemanticsExamples.s0 with heap := MixedAssignmentControls.heap})
private def target (n : Nat) (bound : n < 2^256) :
    State MixedAssignmentControls.C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] :=
  (MixedAssignmentControls.memory.push (integerValue .u256 (n : Int) (amount_range n bound))).push
    (integerValue .u8 129 (by decide))
private def sourceObserved (op : Op) (n : Nat) (bound : n < 2^256)
    (checked : Bool) (p : Roadmap.Pipeline) (fuel : Nat) : Option Int :=
  match (Source.evalE (MixedAssignmentControls.globals p) {Source.SemanticsExamples.F0 with checked := checked}
      (fuel+3) (.shiftLike op.source (.local (.here : Source.Idx _ (.int .u8)))
        (.local (.there .here)) rfl)).run (source n bound) with
  | (.ok (.val (.int z _)),_) => some z
  | _ => none
private def nativeObserved (op : Op) (n : Nat) (bound : n < 2^256) : Option Int :=
  ((value op 8 (by decide) (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
    (target n bound)).toOption.map (·.val)

private theorem observed (op : Op) (n : Nat) (bound : n < 2^256)
    (checked : Bool) (p : Roadmap.Pipeline) (fuel : Nat) :
    sourceObserved op n bound checked p fuel = some ((UnsignedNarrowing.ty 8 (by decide)).wrap
      (op.calculate 8 129 (n : Int))) ∧
    nativeObserved op n bound = some ((UnsignedNarrowing.ty 8 (by decide)).wrap
      (op.calculate 8 129 (n : Int))) := by
  have runs := transport (MixedAssignmentControls.globals p)
    {Source.SemanticsExamples.F0 with checked := checked} fuel (source n bound) (target n bound)
    op 8 (by decide) 256 (by decide) .here (.there .here) .here (.there .here) 129 (n : Int)
    (by decide) (amount_range n bound) rfl rfl rfl rfl
  constructor
  · unfold sourceObserved
    rw [runs.1]
    rfl
  · unfold nativeObserved
    rw [runs.2.1]
    rfl

/-- Actual Source/native runs reject a missing uint8 mask, reversed shift direction, and narrowing the uint256 amount modulo 256. Both modes/pipelines include the left-width and word-width boundaries. -/
theorem regressions_rejected (checked : Bool) (p : Roadmap.Pipeline) (fuel : Nat) :
    sourceObserved .left 1 (by decide) checked p fuel = some 2 ∧
    nativeObserved .left 1 (by decide) = some 2 ∧
    nativeObserved .left 1 (by decide) ≠ some 258 ∧
    sourceObserved .right 1 (by decide) checked p fuel = some 64 ∧
    nativeObserved .right 1 (by decide) = some 64 ∧
    nativeObserved .right 1 (by decide) ≠ nativeObserved .left 1 (by decide) ∧
    ∀ op, sourceObserved op 8 (by decide) checked p fuel = some 0 ∧
      nativeObserved op 8 (by decide) = some 0 ∧
      sourceObserved op 256 (by decide) checked p fuel = some 0 ∧
      nativeObserved op 256 (by decide) = some 0 ∧
      nativeObserved op 256 (by decide) ≠ some 129 := by
  have left := observed .left 1 (by decide) checked p fuel
  have right := observed .right 1 (by decide) checked p fuel
  change sourceObserved .left 1 _ checked p fuel = some 2 ∧
    nativeObserved .left 1 _ = some 2 at left
  change sourceObserved .right 1 _ checked p fuel = some 64 ∧
    nativeObserved .right 1 _ = some 64 at right
  refine ⟨left.1,left.2,?_,right.1,right.2,?_,?_⟩
  · rw [left.2]; decide
  · rw [left.2,right.2]; decide
  · intro op
    have width := observed op 8 (by decide) checked p fuel
    have word := observed op 256 (by decide) checked p fuel
    change sourceObserved op 8 _ checked p fuel = some 0 ∧ nativeObserved op 8 _ = some 0 at width
    change sourceObserved op 256 _ checked p fuel = some 0 ∧ nativeObserved op 256 _ = some 0 at word
    exact ⟨width.1,width.2,word.1,word.2,by rw [word.2]; decide⟩

end Solidity.Lowering.G16.UnsignedShiftControls

/-- info: 'Solidity.Lowering.G16.UnsignedShiftControls.regressions_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.UnsignedShiftControls.regressions_rejected
