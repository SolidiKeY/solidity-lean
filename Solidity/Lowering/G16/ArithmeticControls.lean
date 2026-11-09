import Solidity.Lowering.G16.Arithmetic
import Solidity.Lowering.V07.WordCastControls

/-! Inhabited clients and negative controls for the generic wrapping arithmetic
helper. These check actual Source/target instances without new native axioms. -/
namespace Solidity.Lowering.G16.ArithmeticControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.Arithmetic

/-- A concrete mixed-location input family witnesses the generic theorem's
premises for each operation, width, sign and pipeline. -/
def client (t : Source.IntTy) (op : RingOp) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  wrapping_transport (MixedAssignmentControls.globals pipeline) Source.SemanticsExamples.F0 fuel
    (WordCastControls.source t x y hx hy) (WordCastControls.target t x y hx hy) t op
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t x y hx hy)
    true false x y hx hy rfl rfl

/-- Guards against dropping the unsigned mask, using unsigned interpretation
for signed output, and reversing subtraction operands. -/
theorem wrong_wrapping_rejected :
    Source.IntTy.u8.wrap (RingOp.calculate .add 255 1) ≠ 256 ∧
    (SignedWidthCasts.ty 8 (by decide)).wrap (RingOp.calculate .add 127 1) ≠ 128 ∧
    Source.IntTy.u8.wrap (RingOp.calculate .sub 0 1) ≠
      Source.IntTy.u8.wrap (RingOp.calculate .sub 1 0) := by
  decide

/-- Exercises the headline on an overflowing unsigned addition, rather than
only checking its mathematical observation separately. -/
def unsigned_boundary (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client .u8 .add 255 1 (by decide) (by decide) pipeline fuel

/-- Exercises the same generic statement on signed overflow. -/
def signed_boundary (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client (SignedWidthCasts.ty 8 (by decide)) .add 127 1 (by decide) (by decide) pipeline fuel


/-- Both pipeline orders instantiate the assignment/read clause on genuine
mixed local/memory/storage states, for every operation, width and sign. -/
def assignment_client (t : Source.IntTy) (op : RingOp) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  wrapping_assignment_transport (MixedAssignmentControls.globals pipeline)
    Source.SemanticsExamples.F0 fuel (WordCastControls.source t x y hx hy)
    (WordCastControls.target t x y hx hy) t op
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t x y hx hy)
    false true x y hx hy rfl rfl

/-- Observe the actual Source execution of `(i = a) - i`, starting with
`a = 3` and `i = 1`, without assuming either expression's execution. -/
def assignmentObserved (pipeline : Roadmap.Pipeline) (fuel : Nat) : Source.R (Option Int) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := false} (fuel+4)
    (.binary RingOp.sub.source
      (.assign (.local (WordCastControls.si .u8 false)) (.local (WordCastControls.si .u8 true)))
      (.local (WordCastControls.si .u8 false)))).run
    (WordCastControls.source .u8 3 1 (by decide) (by decide))).1.map
      (fun result => match result with | .val value => value.key)

/-- Guards against silently choosing the same operand order for both
pipelines. This compares actual Source runs supplied by inhabited clients. -/
theorem wrong_assignment_order_rejected (fuel : Nat) :
    assignmentObserved .legacy fuel ≠ assignmentObserved .viaIR fuel := by
  have legacy := (assignment_client .u8 .sub 3 1 (by decide) (by decide) .legacy fuel).1
  have viaIR := (assignment_client .u8 .sub 3 1 (by decide) (by decide) .viaIR fuel).1
  unfold assignmentObserved
  rw [legacy,viaIR]
  intro impossible
  cases impossible

end Solidity.Lowering.G16.ArithmeticControls

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_wrapping_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_wrapping_rejected

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_assignment_order_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_assignment_order_rejected
