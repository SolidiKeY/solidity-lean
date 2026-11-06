import Solidity.Lowering.V07.Scalar

/-! Value-level conversions use the published Source operations. These are
not certificates for production compilation or declaration admission. -/
namespace Solidity.Lowering.V07
variable {D : Source.Layout}

theorem implicit_integer_range (a b : Source.IntTy) (allowed : a.implicit b = true)
    (x : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) : b.lo ≤ x ∧ x ≤ b.hi := by
  have h := Source.implicit_int_range allowed
  omega

theorem implicit_integer_run (a b : Source.IntTy) (allowed : a.implicit b = true)
    (x : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) :
    Source.convVal (.int b) (.int x hx : Source.Val D (.int a)) =
      .ok (.int x (implicit_integer_range a b allowed x hx)) := by
  simp only [Source.convVal, Source.mkInt, dif_pos (implicit_integer_range a b allowed x hx)]
  rfl

theorem implicit_integer_transport (a b : Source.IntTy) (allowed : a.implicit b = true)
    (x : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) :
    PrimTy.num? (integerValue a x hx) =
      PrimTy.num? (integerValue b x (implicit_integer_range a b allowed x hx)) := by
  rw [integer_observe, integer_observe]

theorem explicit_integer_run (a b : Source.IntTy) (x : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) :
    Source.convExplicitVal (.int b) (.int x hx : Source.Val D (.int a)) =
      .ok (.int (b.wrap x) (b.wrap_mem x)) := rfl

theorem explicit_integer_transport (b : Source.IntTy) (x : Int) :
    IntValueRel b (Source.intWrap b x : Source.Val D (.int b))
      (integerValue b (b.wrap x) (b.wrap_mem x)) := integer_related b _ _

theorem address_conversion (a b : Bool) (x : Solidity.Roadmap.Address) :
    Source.convVal (.address b) (.address x : Source.Val D (.address a)) =
      .ok (.address x) := rfl

theorem udvt_identity (d : Source.DeclName) (v : Source.Val D (.udvt d)) :
    Source.convVal (.udvt d) v = .ok v := by
  change (if h : d = d then pure (h ▸ v) else Source.stuck "user-defined value type") = _
  rw [dif_pos rfl]
  rfl

end Solidity.Lowering.V07
