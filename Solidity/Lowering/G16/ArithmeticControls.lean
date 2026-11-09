import Solidity.Lowering.G16.Arithmetic
import Solidity.Lowering.V07.WordCastControls

/-! Inhabited Source/native arithmetic clients and negative controls; no new native axioms. -/
namespace Solidity.Lowering.G16.ArithmeticControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.Arithmetic

/-- Mixed-location clients witness premises for every operation, width, sign and pipeline. -/
def client (t : Source.IntTy) (op : RingOp) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  wrapping_transport (MixedAssignmentControls.globals pipeline) Source.SemanticsExamples.F0 fuel
    (WordCastControls.source t x y hx hy) (WordCastControls.target t x y hx hy) t op
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t x y hx hy)
    true false x y hx hy rfl rfl

/-- Reject lost unsigned masks, unsigned interpretation of signed outputs, and reversed subtraction. -/
theorem wrong_wrapping_rejected :
    Source.IntTy.u8.wrap (RingOp.calculate .add 255 1) ≠ 256 ∧
    (SignedWidthCasts.ty 8 (by decide)).wrap (RingOp.calculate .add 127 1) ≠ 128 ∧
    Source.IntTy.u8.wrap (RingOp.calculate .sub 0 1) ≠
      Source.IntTy.u8.wrap (RingOp.calculate .sub 1 0) := by
  decide

/-- Apply the headline to actual unsigned addition overflow. -/
def unsigned_boundary (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client .u8 .add 255 1 (by decide) (by decide) pipeline fuel

/-- Apply the same headline to signed overflow. -/
def signed_boundary (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client (SignedWidthCasts.ty 8 (by decide)) .add 127 1 (by decide) (by decide) pipeline fuel


/-- Assignment/read clients for both pipelines, every operation/width/sign and mixed local/memory/storage states. -/
def assignment_client (t : Source.IntTy) (op : RingOp) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  wrapping_assignment_transport (MixedAssignmentControls.globals pipeline)
    Source.SemanticsExamples.F0 fuel (WordCastControls.source t x y hx hy)
    (WordCastControls.target t x y hx hy) t op
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t x y hx hy)
    false true x y hx hy rfl rfl

/-- Observe actual Source `(i = a) - i` from a=3, i=1; neither operand's execution is assumed. -/
def assignmentObserved (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := false} (fuel+4)
    (.binary RingOp.sub.source
      (.assign (.local (WordCastControls.si .u8 false)) (.local (WordCastControls.si .u8 true)))
      (.local (WordCastControls.si .u8 false)))).run
    (WordCastControls.source .u8 3 1 (by decide) (by decide))).1.map
      (fun result => match result with | .val value => value.key)

/-- Reject identical pipeline orders by comparing actual Source runs from inhabited clients. -/
theorem wrong_assignment_order_rejected (fuel : Nat) :
    assignmentObserved .legacy fuel ≠ assignmentObserved .viaIR fuel := by
  have legacy := (assignment_client .u8 .sub 3 1 (by decide) (by decide) .legacy fuel).1
  have viaIR := (assignment_client .u8 .sub 3 1 (by decide) (by decide) .viaIR fuel).1
  unfold assignmentObserved
  rw [legacy,viaIR]
  intro impossible
  cases impossible


/-- Mixed-location unsigned clients for all widths/operators/modes/pipelines, including overflow and zero. -/
def checked_client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (op : RingOp) (checked : Bool) (x y : Int)
    (hx : (UnsignedNarrowing.ty bits valid).lo ≤ x ∧ x ≤ (UnsignedNarrowing.ty bits valid).hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  CheckedUnsigned.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source (UnsignedNarrowing.ty bits valid) x y hx hy)
    (WordCastControls.target (UnsignedNarrowing.ty bits valid) x y hx hy)
    bits valid op (WordCastControls.si _) (WordCastControls.ti _)
    (WordCastControls.initial _ x y hx hy) true false x y hx hy rfl rfl

/-- Actual Source result; the observation keeps panics distinct from values. -/
def checkedObserved (checked : Bool) (op : RingOp) (x y : Int)
    (hx : (UnsignedNarrowing.ty 8 (by decide)).lo ≤ x ∧ x ≤ (UnsignedNarrowing.ty 8 (by decide)).hi)
    (hy : (UnsignedNarrowing.ty 8 (by decide)).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+3)
    (.binary op.source (.local (WordCastControls.si (UnsignedNarrowing.ty 8 (by decide)) true))
      (.local (WordCastControls.si (UnsignedNarrowing.ty 8 (by decide)) false)))).run
    (WordCastControls.source (UnsignedNarrowing.ty 8 (by decide)) x y hx hy)).1.map
      (fun result => match result with | .val value => value.key)

/-- Reject erasing any ring overflow guard using actual Source runs from inhabited clients. -/
theorem wrong_checked_ring_rejected (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    checkedObserved true .add 255 1 (by decide) (by decide) pipeline fuel ≠
      checkedObserved false .add 255 1 (by decide) (by decide) pipeline fuel ∧
    checkedObserved true .sub 0 1 (by decide) (by decide) pipeline fuel ≠
      checkedObserved false .sub 0 1 (by decide) (by decide) pipeline fuel ∧
    checkedObserved true .mul 16 16 (by decide) (by decide) pipeline fuel ≠
      checkedObserved false .mul 16 16 (by decide) (by decide) pipeline fuel := by
  have ca := (checked_client 8 (by decide) .add true 255 1 (by decide) (by decide) pipeline fuel).1
  have ua := (checked_client 8 (by decide) .add false 255 1 (by decide) (by decide) pipeline fuel).1
  have cs := (checked_client 8 (by decide) .sub true 0 1 (by decide) (by decide) pipeline fuel).1
  have us := (checked_client 8 (by decide) .sub false 0 1 (by decide) (by decide) pipeline fuel).1
  have cm := (checked_client 8 (by decide) .mul true 16 16 (by decide) (by decide) pipeline fuel).1
  have um := (checked_client 8 (by decide) .mul false 16 16 (by decide) (by decide) pipeline fuel).1
  unfold checkedObserved
  rw [ca,ua,cs,us,cm,um]
  change ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some 0)) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some 255)) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some 0))
  simp only [ne_eq,reduceCtorEq,not_false_eq_true,and_self]

/-- Exercise checked native multiplication at zero; division must remain behind its lazy zero test. -/
def zero_multiplier (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  checked_client 8 (by decide) .mul true 0 255 (by decide) (by decide) pipeline fuel

end Solidity.Lowering.G16.ArithmeticControls

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_wrapping_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_wrapping_rejected

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_assignment_order_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_assignment_order_rejected

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_checked_ring_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_checked_ring_rejected
