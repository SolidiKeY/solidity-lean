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

end Solidity.Lowering.G16.ComparisonControls

/-- info: 'Solidity.Lowering.G16.ComparisonControls.wrong_comparison_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ComparisonControls.wrong_comparison_rejected
