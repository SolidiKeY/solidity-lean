import Solidity.Lowering.V07.BooleanComparisonControls
import Solidity.Lowering.G16.Comparisons
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.AddressConversions
import Solidity.Lowering.V07.SignedWidthCasts

/-! Concrete scalar-key comparison clients and negative controls. -/
namespace Solidity.Lowering.G16.ComparisonControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.Comparisons

/-- All valid integer widths/signs and comparison opcodes have concrete
initial observations in the existing mixed-location fixture. -/
def integer_client (t : Source.IntTy) (op : BinOp)
    (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  transport (MixedAssignmentControls.globals pipeline) Source.SemanticsExamples.F0 fuel
    (WordCastControls.source t x y hx hy) (WordCastControls.target t x y hx hy) t op accepts returns
    .here (.there .here) .here (.there .here) (.int x hx) (.int y hy) x y hx hy
    rfl rfl rfl rfl rfl rfl

/-- The same theorem applies to intrinsically address-typed Source locals,
without replacing their Source type by an integer. -/
def address_client (a b : Roadmap.Address) (op : BinOp)
    (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  let source : Source.EMState MixedAssignmentControls.E [.address false,.address false] :=
    (.cons (.address a) (.cons (.address b) .nil),
      (WordCastControls.source .u8 0 1 (by decide) (by decide)).2)
  transport (MixedAssignmentControls.globals pipeline) Source.SemanticsExamples.F0 fuel source
    (WordCastControls.target AddressConversions.ty a.val b.val
      (AddressConversions.address_range a) (AddressConversions.address_range b))
    AddressConversions.ty op accepts returns .here (.there .here) .here (.there .here)
    (.address a) (.address b) a.val b.val (AddressConversions.address_range a)
    (AddressConversions.address_range b) rfl rfl rfl rfl rfl rfl

/-- Guards against unsigned reinterpretation of signed comparison inputs and
reversal of scalar comparison operands. -/
theorem wrong_comparison_rejected {D : Source.Layout} :
    Source.cmpVal .lt
      (.int (-1) (by decide) : Source.Val D (.int (SignedWidthCasts.ty 8 (by decide))))
      (.int 0 (by decide)) ≠ .ok false ∧
    Source.cmpVal .lt (.address ⟨1,by decide⟩ : Source.Val D (.address false))
      (.address ⟨2,by decide⟩) ≠ .ok false ∧
    Source.cmpVal .lt (.address ⟨2,by decide⟩ : Source.Val D (.address false))
      (.address ⟨1,by decide⟩) ≠ .ok true := by
  change (Except.ok true : Source.R Bool) ≠ .ok false ∧
    (Except.ok true : Source.R Bool) ≠ .ok false ∧
    (Except.ok false : Source.R Bool) ≠ .ok true
  exact ⟨(by intro h; cases h),(by intro h; cases h),(by intro h; cases h)⟩

def assignment_integer_client (t : Source.IntTy) (op : BinOp)
    (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source t x y hx hy) (WordCastControls.target t x y hx hy) t op accepts returns
    (.there .here) .here (.there .here) .here (.int x hx) (.int y hy) x y hx hy
    rfl rfl rfl rfl rfl rfl

def assignment_address_client (a b : Roadmap.Address) (op : BinOp)
    (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  let source : Source.EMState MixedAssignmentControls.E [.address false,.address false] :=
    (.cons (.address a) (.cons (.address b) .nil),
      (WordCastControls.source .u8 0 1 (by decide) (by decide)).2)
  assignment_transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel source
    (WordCastControls.target AddressConversions.ty a.val b.val
      (AddressConversions.address_range a) (AddressConversions.address_range b))
    AddressConversions.ty op accepts returns (.there .here) .here (.there .here) .here
    (.address a) (.address b) a.val b.val (AddressConversions.address_range a)
    (AddressConversions.address_range b) rfl rfl rfl rfl rfl rfl

def assignmentObserved (t : Source.IntTy) (op : BinOp) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    Source.R (Source.RVal MixedAssignmentControls.E.layout .bool) :=
  ((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.compare (NumericComparisons.sourceOp op)
      (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run
      (WordCastControls.source t x y hx hy)).1

def assignmentWritten (t : Source.IntTy) (op : BinOp) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Int :=
  (((Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.compare (NumericComparisons.sourceOp op)
      (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run
      (WordCastControls.source t x y hx hy)).2.1.get (.there .here)).key

private theorem assignment_observed_run (t : Source.IntTy) (op : BinOp)
    (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    assignmentObserved t op x y hx hy checked pipeline fuel =
      (Source.cmpVal (NumericComparisons.sourceOp op)
        (.int x hx : Source.Val MixedAssignmentControls.E.layout (.int t))
        (if pipeline = .legacy then .int y hy else .int x hx)).map (fun r => .val (.bool r)) := by
  obtain ⟨result,computed,source,native⟩ :=
    assignment_integer_client t op accepts returns x y hx hy checked pipeline fuel
  unfold assignmentObserved
  dsimp only [MixedAssignmentControls.globals] at computed
  rw [source,computed]
  rfl

private theorem assignment_written_run (t : Source.IntTy) (op : BinOp)
    (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    assignmentWritten t op x y hx hy checked pipeline fuel = some x := by
  obtain ⟨result,computed,source,native⟩ :=
    assignment_integer_client t op accepts returns x y hx hy checked pipeline fuel
  unfold assignmentWritten
  rw [source,source_locals_get_set]
  rfl

/-- Reject erased capture order and dropped assignment writes on actual comparison executions in both modes. -/
theorem wrong_assignment_comparison_rejected (checked : Bool) (fuel : Nat) :
    assignmentObserved .u8 .gt 3 1 (by decide) (by decide) checked .legacy fuel ≠
      assignmentObserved .u8 .gt 3 1 (by decide) (by decide) checked .viaIR fuel ∧
    assignmentObserved .u8 .eqB 3 1 (by decide) (by decide) checked .legacy fuel ≠
      assignmentObserved .u8 .eqB 3 1 (by decide) (by decide) checked .viaIR fuel ∧
    assignmentWritten .u8 .gt 3 1 (by decide) (by decide) checked .legacy fuel ≠ some 1 := by
  rw [assignment_observed_run .u8 .gt rfl rfl,assignment_observed_run .u8 .gt rfl rfl,
    assignment_observed_run .u8 .eqB rfl rfl,assignment_observed_run .u8 .eqB rfl rfl,
    assignment_written_run .u8 .gt rfl rfl]
  refine ⟨?_,?_,?_⟩ <;> intro impossible <;> cases impossible

end Solidity.Lowering.G16.ComparisonControls

/-- info: 'Solidity.Lowering.G16.ComparisonControls.wrong_comparison_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ComparisonControls.wrong_comparison_rejected

/-- info: 'Solidity.Lowering.G16.ComparisonControls.wrong_assignment_comparison_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ComparisonControls.wrong_assignment_comparison_rejected

namespace Solidity.Lowering.G16.BooleanComparisonControls
open Solidity.Lowering.V07

private def sampleSource := BooleanComparisonControls.source false true
private def sampleTarget := BooleanComparisonControls.target false true

private def sourceRun (ne checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  (Source.evalE (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} (fuel+4)
    (.compare (BooleanComparisons.sourceOp ne)
      (.assign (.local .here) (.local (.there .here))) (.local .here))).run sampleSource

private def sourceObserved (ne checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Bool :=
  match (sourceRun ne checked pipeline fuel).1 with
  | .ok (.val (.bool b)) => some b
  | _ => none

private def sourceWritten (ne checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) : Option Bool :=
  match (sourceRun ne checked pipeline fuel).2.1.get .here with
  | .bool b => some b

private def nativeObserved (ne : Bool) (pipeline : Roadmap.Pipeline) : Option Bool :=
  match (BooleanComparisons.operand ne pipeline .here (.there .here)).run sampleTarget with
  | .ok (_, .prim b) => some b
  | .error _ => none

private def nativeWritten (ne : Bool) (pipeline : Roadmap.Pipeline) : Option Bool :=
  match (BooleanComparisons.operand ne pipeline .here (.there .here)).run sampleTarget with
  | .ok (out,_) => some (TEnv.get .here out.st.env)
  | .error _ => none

private theorem sample_run (ne checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    sourceObserved ne checked pipeline fuel =
      some (BooleanComparisons.answer ne true (if pipeline = .legacy then false else true)) ∧
    nativeObserved ne pipeline =
      some (BooleanComparisons.answer ne true (if pipeline = .legacy then false else true)) ∧
    sourceWritten ne checked pipeline fuel = some true ∧ nativeWritten ne pipeline = some true := by
  have runs := BooleanComparison.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel sampleSource sampleTarget ne
    .here (.there .here) .here (.there .here) true false rfl rfl rfl rfl
  have native := runs.2
  dsimp only [MixedAssignmentControls.globals] at native
  refine ⟨?_,?_,?_,?_⟩
  · unfold sourceObserved sourceRun
    rw [runs.1]
    rfl
  · unfold nativeObserved
    rw [native]
  · unfold sourceWritten sourceRun
    rw [runs.1]
    rfl
  · unfold nativeWritten
    rw [native]
    rfl

/-- Guards both Boolean comparison operators against losing the pre-assignment capture; actual Source/native observations agree and both callers record the write in either mode. -/
theorem wrong_capture_rejected (ne checked : Bool) (fuel : Nat) :
    sourceObserved ne checked .legacy fuel ≠ sourceObserved ne checked .viaIR fuel ∧
    ∀ pipeline, sourceObserved ne checked pipeline fuel = nativeObserved ne pipeline ∧
      sourceWritten ne checked pipeline fuel = some true ∧ nativeWritten ne pipeline = some true := by
  refine ⟨?_,?_⟩
  · rw [(sample_run ne checked .legacy fuel).1,(sample_run ne checked .viaIR fuel).1]
    cases ne <;> intro impossible <;> cases impossible
  · intro pipeline
    obtain ⟨source,native,written,target⟩ := sample_run ne checked pipeline fuel
    exact ⟨source.trans native.symm,written,target⟩

end Solidity.Lowering.G16.BooleanComparisonControls

/-- info: 'Solidity.Lowering.G16.BooleanComparisonControls.wrong_capture_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.BooleanComparisonControls.wrong_capture_rejected
