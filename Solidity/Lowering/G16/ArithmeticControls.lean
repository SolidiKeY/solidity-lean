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


/-- Inhabited signed ring clients for all valid widths, operators, modes and pipelines. -/
def signed_checked_client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (op : RingOp) (checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty bits valid).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty bits valid).hi)
    (hy : (SignedWidthCasts.ty bits valid).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  CheckedSigned.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source (SignedWidthCasts.ty bits valid) x y hx hy)
    (WordCastControls.target (SignedWidthCasts.ty bits valid) x y hx hy)
    bits valid op (WordCastControls.si _) (WordCastControls.ti _)
    (WordCastControls.initial _ x y hx hy) true false x y hx hy rfl rfl

/-- Observe the actual signed Source result while retaining panic-versus-value distinctions. -/
def signedObserved (checked : Bool) (op : RingOp) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+3)
    (.binary op.source (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) true))
      (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) false)))).run
    (WordCastControls.source (SignedWidthCasts.ty 8 (by decide)) x y hx hy)).1.map
      (fun result => match result with | .val value => value.key)

private theorem signed_observed_run (checked : Bool) (op : RingOp) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    signedObserved checked op x y hx hy pipeline fuel =
      if checked = true ∧ ¬ ((SignedWidthCasts.ty 8 (by decide)).lo ≤ op.calculate x y ∧
          op.calculate x y ≤ (SignedWidthCasts.ty 8 (by decide)).hi) then
        .error (.revert (Source.panicData .arithmetic))
      else .ok (some ((SignedWidthCasts.ty 8 (by decide)).wrap (op.calculate x y))) := by
  have whole := signed_checked_client 8 (by decide) op checked x y hx hy pipeline fuel
  unfold signedObserved
  by_cases failed : checked = true ∧ ¬ ((SignedWidthCasts.ty 8 (by decide)).lo ≤ op.calculate x y ∧
    op.calculate x y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
  · simp only [if_pos failed] at whole
    rw [whole.1,if_pos failed]
    rfl
  · simp only [if_neg failed] at whole
    rw [whole.1,if_neg failed]
    rfl

/-- Reject lost signed overflow guards, including minimum times minus one, using actual Source runs. -/
theorem wrong_signed_ring_rejected (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    signedObserved true .add 127 1 (by decide) (by decide) pipeline fuel ≠
      signedObserved false .add 127 1 (by decide) (by decide) pipeline fuel ∧
    signedObserved true .sub (-128) 1 (by decide) (by decide) pipeline fuel ≠
      signedObserved false .sub (-128) 1 (by decide) (by decide) pipeline fuel ∧
    signedObserved true .mul (-128) (-1) (by decide) (by decide) pipeline fuel ≠
      signedObserved false .mul (-128) (-1) (by decide) (by decide) pipeline fuel := by
  rw [signed_observed_run,signed_observed_run,signed_observed_run,signed_observed_run,
    signed_observed_run,signed_observed_run]
  change ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some (-128))) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some 127)) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some (-128)))
  simp only [ne_eq,reduceCtorEq,not_false_eq_true,and_self]

/-- Exercise the checked native zero branch before any quotient or minimum rejection. -/
def signed_zero_multiplier (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  signed_checked_client 8 (by decide) .mul true 0 (-128) (by decide) (by decide) pipeline fuel

/-- The minimum is not globally excluded: multiplying it by positive one succeeds. -/
def signed_minimum_success (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  signed_checked_client 8 (by decide) .mul true (-128) 1 (by decide) (by decide) pipeline fuel

/-- Inhabited signed quotient/remainder clients retain local, memory and storage agreement. -/
def signed_quotrem_client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty bits valid).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty bits valid).hi)
    (hy : (SignedWidthCasts.ty bits valid).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  SignedQuotRem.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source (SignedWidthCasts.ty bits valid) x y hx hy)
    (WordCastControls.target (SignedWidthCasts.ty bits valid) x y hx hy)
    bits valid rem (WordCastControls.si _) (WordCastControls.ti _)
    (WordCastControls.initial _ x y hx hy) true false x y hx hy rfl rfl

def signedQuotRemObserved (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+3)
    (.binary (SignedQuotRem.sourceOp rem) (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) true))
      (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) false)))).run
    (WordCastControls.source (SignedWidthCasts.ty 8 (by decide)) x y hx hy)).1.map
      (fun result => match result with | .val value => value.key)

private theorem signed_quotrem_observed_run (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    signedQuotRemObserved rem checked x y hx hy pipeline fuel =
      if y = 0 then .error (.revert (Source.panicData .divZero)) else
      if checked = true ∧ rem = false ∧ x = (SignedWidthCasts.ty 8 (by decide)).lo ∧ y = -1 then
        .error (.revert (Source.panicData .arithmetic)) else
        .ok (some ((SignedWidthCasts.ty 8 (by decide)).wrap (SignedQuotRem.calculate rem x y))) := by
  have whole := signed_quotrem_client 8 (by decide) rem checked x y hx hy pipeline fuel
  unfold signedQuotRemObserved
  by_cases iszero : y = 0
  · simp only [if_pos iszero] at whole
    rw [whole.1,if_pos iszero]
    rfl
  · simp only [if_neg iszero] at whole
    rw [if_neg iszero]
    by_cases failed : checked = true ∧ rem = false ∧ x = (SignedWidthCasts.ty 8 (by decide)).lo ∧ y = -1
    · simp only [if_pos failed] at whole
      rw [whole.1,if_pos failed]
      rfl
    · simp only [if_neg failed] at whole
      rw [whole.1,if_neg failed]
      rfl

/-- Reject zero-as-success, erased quotient overflow, conflated remainder and reversed operands using actual Source runs. -/
theorem wrong_signed_quotrem_rejected (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    signedQuotRemObserved false false 1 0 (by decide) (by decide) pipeline fuel ≠ .ok (some 0) ∧
    signedQuotRemObserved false true (-128) (-1) (by decide) (by decide) pipeline fuel ≠
      signedQuotRemObserved false false (-128) (-1) (by decide) (by decide) pipeline fuel ∧
    signedQuotRemObserved true true (-128) (-1) (by decide) (by decide) pipeline fuel ≠
      signedQuotRemObserved false true (-128) (-1) (by decide) (by decide) pipeline fuel ∧
    signedQuotRemObserved false false (-1) (-128) (by decide) (by decide) pipeline fuel ≠
      signedQuotRemObserved false false (-128) (-1) (by decide) (by decide) pipeline fuel := by
  simp only [signed_quotrem_observed_run]
  change ((Except.error (.revert (Source.panicData .divZero)) : Source.R (Option Int)) ≠ .ok (some 0)) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some (-128))) ∧
    ((Except.ok (some 0) : Source.R (Option Int)) ≠ .error (.revert (Source.panicData .arithmetic))) ∧
    ((Except.ok (some 0) : Source.R (Option Int)) ≠ .ok (some (-128)))
  simp only [ne_eq,reduceCtorEq,not_false_eq_true,Except.ok.injEq,Option.some.injEq,and_self]

/-- Both modes and operators have native zero-panic clients, not merely a nonzero-divisor instance. -/
def signed_quotrem_zero (rem checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  signed_quotrem_client 8 (by decide) rem checked 1 0 (by decide) (by decide) pipeline fuel

/-- The minimum divided by minus one remains in all four native operator/mode instances. -/
def signed_quotrem_minimum (rem checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  signed_quotrem_client 8 (by decide) rem checked (-128) (-1) (by decide) (by decide) pipeline fuel

/-- Inhabited captured ring clients across all widths/signs, modes and pipelines. -/
def checked_assignment_client (t : Source.IntTy) (op : RingOp) (checked : Bool) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  CheckedAssignment.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source t x y hx hy) (WordCastControls.target t x y hx hy) t op
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t x y hx hy)
    false true x y hx hy rfl rfl

def checkedAssignmentObserved (t : Source.IntTy) (op : RingOp) (checked : Bool) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.binary op.source (.assign (.local (WordCastControls.si t false)) (.local (WordCastControls.si t true)))
      (.local (WordCastControls.si t false)))).run (WordCastControls.source t x y hx hy)).1.map
        (fun result => match result with | .val value => value.key)

def checkedAssignmentWritten (t : Source.IntTy) (op : RingOp) (checked : Bool) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Int :=
  (((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.binary op.source (.assign (.local (WordCastControls.si t false)) (.local (WordCastControls.si t true)))
      (.local (WordCastControls.si t false)))).run (WordCastControls.source t x y hx hy)).2.1.get
        (WordCastControls.si t false)).key

private theorem assignment_observed_run (t : Source.IntTy) (op : RingOp) (checked : Bool) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    checkedAssignmentObserved t op checked x y hx hy pipeline fuel =
      if checked = true ∧ ¬ (t.lo ≤ op.calculate x (if pipeline = .legacy then y else x) ∧
          op.calculate x (if pipeline = .legacy then y else x) ≤ t.hi) then
        .error (.revert (Source.panicData .arithmetic)) else
        .ok (some (t.wrap (op.calculate x (if pipeline = .legacy then y else x)))) := by
  have actual := (checked_assignment_client t op checked x y hx hy pipeline fuel).1
  unfold checkedAssignmentObserved
  rw [actual]
  dsimp only [MixedAssignmentControls.globals]
  by_cases failed : checked = true ∧ ¬ (t.lo ≤ op.calculate x (if pipeline = .legacy then y else x) ∧
      op.calculate x (if pipeline = .legacy then y else x) ≤ t.hi)
  · simp only [if_pos failed]
    rfl
  · simp only [if_neg failed]
    rfl

private theorem assignment_written_run (t : Source.IntTy) (op : RingOp) (checked : Bool) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    checkedAssignmentWritten t op checked x y hx hy pipeline fuel = some x := by
  have actual := (checked_assignment_client t op checked x y hx hy pipeline fuel).1
  unfold checkedAssignmentWritten
  rw [actual,source_locals_get_set]
  rfl

/-- Reject pipeline order erasure for all three operators and both signs, and erasing a write before Source panic. -/
theorem wrong_checked_capture_rejected (fuel : Nat) :
    checkedAssignmentObserved .u8 .add true 200 0 (by decide) (by decide) .legacy fuel ≠
      checkedAssignmentObserved .u8 .add true 200 0 (by decide) (by decide) .viaIR fuel ∧
    checkedAssignmentObserved (SignedWidthCasts.ty 8 (by decide)) .add true 100 (-100) (by decide) (by decide) .legacy fuel ≠
      checkedAssignmentObserved (SignedWidthCasts.ty 8 (by decide)) .add true 100 (-100) (by decide) (by decide) .viaIR fuel ∧
    checkedAssignmentObserved .u8 .sub true 0 1 (by decide) (by decide) .legacy fuel ≠
      checkedAssignmentObserved .u8 .sub true 0 1 (by decide) (by decide) .viaIR fuel ∧
    checkedAssignmentObserved .u8 .mul true 16 0 (by decide) (by decide) .legacy fuel ≠
      checkedAssignmentObserved .u8 .mul true 16 0 (by decide) (by decide) .viaIR fuel ∧
    checkedAssignmentWritten .u8 .add true 200 0 (by decide) (by decide) .viaIR fuel ≠ some 0 := by
  simp only [assignment_observed_run,assignment_written_run]
  change ((Except.ok (some 200) : Source.R (Option Int)) ≠ .error (.revert (Source.panicData .arithmetic))) ∧
    ((Except.ok (some 0) : Source.R (Option Int)) ≠ .error (.revert (Source.panicData .arithmetic))) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some 0)) ∧
    ((Except.ok (some 0) : Source.R (Option Int)) ≠ .error (.revert (Source.panicData .arithmetic))) ∧
    (some (200 : Int) ≠ some 0)
  simp only [ne_eq,reduceCtorEq,not_false_eq_true,Option.some.injEq,true_and]
  decide

def signed_assignment_client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty bits valid).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty bits valid).hi)
    (hy : (SignedWidthCasts.ty bits valid).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  SignedQuotRem.assignment_transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source (SignedWidthCasts.ty bits valid) x y hx hy)
    (WordCastControls.target (SignedWidthCasts.ty bits valid) x y hx hy)
    bits valid rem (WordCastControls.si _) (WordCastControls.ti _)
    (WordCastControls.initial _ x y hx hy) false true x y hx hy rfl rfl

def signedAssignmentObserved (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.binary (SignedQuotRem.sourceOp rem)
      (.assign (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) false))
        (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) true)))
      (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) false)))).run
    (WordCastControls.source (SignedWidthCasts.ty 8 (by decide)) x y hx hy)).1.bind
      (fun result => result.get.map (fun value => value.key))

def signedAssignmentWritten (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Int :=
  (((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.binary (SignedQuotRem.sourceOp rem)
      (.assign (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) false))
        (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) true)))
      (.local (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) false)))).run
    (WordCastControls.source (SignedWidthCasts.ty 8 (by decide)) x y hx hy)).2.1.get
      (WordCastControls.si (SignedWidthCasts.ty 8 (by decide)) false)).key

private theorem signed_assignment_observed_run (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    signedAssignmentObserved rem checked x y hx hy pipeline fuel =
      if (if pipeline = .legacy then y else x) = 0 then
        .error (.revert (Source.panicData .divZero)) else
      if checked = true ∧ rem = false ∧ x = (SignedWidthCasts.ty 8 (by decide)).lo ∧
          (if pipeline = .legacy then y else x) = -1 then
        .error (.revert (Source.panicData .arithmetic)) else
        .ok (some ((SignedWidthCasts.ty 8 (by decide)).wrap
          (SignedQuotRem.calculate rem x (if pipeline = .legacy then y else x)))) := by
  have actual := (signed_assignment_client 8 (by decide) rem checked x y hx hy pipeline fuel).1
  unfold signedAssignmentObserved
  rw [actual]
  dsimp only [MixedAssignmentControls.globals]
  by_cases zero : (if pipeline = .legacy then y else x) = 0
  · simp only [if_pos zero]; rfl
  · simp only [if_neg zero]
    by_cases overflow : checked = true ∧ rem = false ∧ x = (SignedWidthCasts.ty 8 (by decide)).lo ∧
        (if pipeline = .legacy then y else x) = -1
    · simp only [if_pos overflow]; rfl
    · simp only [if_neg overflow]; rfl

private theorem signed_assignment_written_run (rem checked : Bool) (x y : Int)
    (hx : (SignedWidthCasts.ty 8 (by decide)).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (hy : (SignedWidthCasts.ty 8 (by decide)).lo ≤ y ∧ y ≤ (SignedWidthCasts.ty 8 (by decide)).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    signedAssignmentWritten rem checked x y hx hy pipeline fuel = some x := by
  have actual := (signed_assignment_client 8 (by decide) rem checked x y hx hy pipeline fuel).1
  unfold signedAssignmentWritten
  rw [actual,source_locals_get_set]
  rfl

/-- Reject erased capture order, zero/overflow panics, wrapping and prepanic writes on actual Source runs. -/
theorem wrong_signed_assignment_rejected (fuel : Nat) :
    signedAssignmentObserved false true 3 0 (by decide) (by decide) .legacy fuel ≠
      signedAssignmentObserved false true 3 0 (by decide) (by decide) .viaIR fuel ∧
    signedAssignmentObserved true true 5 2 (by decide) (by decide) .legacy fuel ≠
      signedAssignmentObserved true true 5 2 (by decide) (by decide) .viaIR fuel ∧
    signedAssignmentObserved false true (-128) (-1) (by decide) (by decide) .legacy fuel ≠
      signedAssignmentObserved false true (-128) (-1) (by decide) (by decide) .viaIR fuel ∧
    signedAssignmentObserved false true (-128) (-1) (by decide) (by decide) .legacy fuel ≠
      signedAssignmentObserved false false (-128) (-1) (by decide) (by decide) .legacy fuel ∧
    signedAssignmentObserved false false (-128) (-1) (by decide) (by decide) .legacy fuel ≠ .ok (some 128) ∧
    signedAssignmentWritten false true 3 0 (by decide) (by decide) .legacy fuel ≠ some 0 := by
  simp only [signed_assignment_observed_run,signed_assignment_written_run]
  change ((Except.error (.revert (Source.panicData .divZero)) : Source.R (Option Int)) ≠ .ok (some 1)) ∧
    ((Except.ok (some 1) : Source.R (Option Int)) ≠ .ok (some 0)) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some 1)) ∧
    ((Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠ .ok (some (-128))) ∧
    ((Except.ok (some (-128)) : Source.R (Option Int)) ≠ .ok (some 128)) ∧
    ((some 3 : Option Int) ≠ some 0)
  simp only [ne_eq,reduceCtorEq,not_false_eq_true,Except.ok.injEq,Option.some.injEq]
  decide

def powerSource (t : Source.IntTy) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi) :
    Source.EMState MixedAssignmentControls.E
      [.int t,.int (UnsignedNarrowing.ty bits valid),.bytes .memory,.bytes .storage] :=
  (.cons (.int x hx) (.cons (.int y hy) (.cons (.memRef rfl 0)
    (.cons (.storRef rfl MixedAssignmentControls.path) .nil))),
    {Source.SemanticsExamples.s0 with heap := MixedAssignmentControls.heap})

def powerTarget (t : Source.IntTy) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi) :
    State MixedAssignmentControls.C [.val (integerPrim t),.val .uint,.mem bytesR,.alias bytesR] :=
  (MixedAssignmentControls.memory.push (integerValue (UnsignedNarrowing.ty bits valid) y hy)).push
    (integerValue t x hx)

def power_client (t : Source.IntTy) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  TypedPower.transport (MixedAssignmentControls.globals pipeline) Source.SemanticsExamples.F0 fuel
    (powerSource t bits valid x y hx hy) (powerTarget t bits valid x y hx hy) t bits valid
    .here (.there .here) .here (.there .here) x y hx hy rfl rfl rfl rfl

def powerObserved (t : Source.IntTy) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := false} (fuel+3)
    (.shiftLike .exp (.local .here) (.local (.there .here)) rfl)).run
      (powerSource t bits valid x y hx hy)).1.bind (fun result => result.get.map (fun v => v.key))

private theorem power_observed_run (t : Source.IntTy) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    powerObserved t bits valid x y hx hy pipeline fuel = .ok (some (t.wrap (x^y.toNat))) := by
  have actual := (power_client t bits valid x y hx hy pipeline fuel).1
  unfold powerObserved
  rw [actual]
  rfl

/-- Reject lost masks/signs, reversed operands, erased zero-to-zero, wrong parity and narrowed exponents on actual Source runs. -/
theorem wrong_typed_power_rejected (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    powerObserved .u8 8 (by decide) 2 8 (by decide) (by decide) pipeline fuel ≠ .ok (some 256) ∧
    powerObserved (SignedWidthCasts.ty 8 (by decide)) 8 (by decide) (-2) 3
      (by decide) (by decide) pipeline fuel ≠ .ok (some 248) ∧
    powerObserved .u8 8 (by decide) 2 3 (by decide) (by decide) pipeline fuel ≠
      powerObserved .u8 8 (by decide) 3 2 (by decide) (by decide) pipeline fuel ∧
    powerObserved .u8 8 (by decide) 0 0 (by decide) (by decide) pipeline fuel ≠ .ok (some 0) ∧
    powerObserved (SignedWidthCasts.ty 8 (by decide)) 16 (by decide) (-1) 511
      (by decide) (by decide) pipeline fuel ≠ .ok (some 1) ∧
    powerObserved .u8 16 (by decide) 2 256 (by decide) (by decide) pipeline fuel ≠ .ok (some 1) := by
  simp only [power_observed_run,ne_eq,Except.ok.injEq,Option.some.injEq]
  have residue := Source.PowerV2.powMod_residue (-1) 511 256
  have oddWrapped : (SignedWidthCasts.ty 8 (by decide)).wrap ((-1 : Int)^511) = -1 := by
    rw [SignedWidthCasts.wrap_eq,← residue]
    decide
  have big : (2 : Int)^256 = ((2^256 : Nat) : Int) := (Int.natCast_pow 2 256).symm
  rw [show (511 : Int).toNat = 511 from rfl,oddWrapped,show (256 : Int).toNat = 256 from rfl,big]
  decide

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

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_signed_ring_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_signed_ring_rejected

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_signed_quotrem_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_signed_quotrem_rejected

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_checked_capture_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_checked_capture_rejected

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_signed_assignment_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_signed_assignment_rejected

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_typed_power_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_typed_power_rejected
