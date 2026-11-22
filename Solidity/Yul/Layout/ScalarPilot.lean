import Solidity.Yul.Layout.Geometric

/-!
# The Scalar pilot correspondence of the geometry

`scalarPilot` is the scalar part of `Shrink.LayoutView.ScalarPilot` for
`geometry`, at every allocator. `scalar` and `memoryScalar` are the fields of
`geometric`; `scalarPathRead` and `scalarPathWrite` follow from them for both
slot regions, through the `.scalar` case of `Geometry.read`/`Geometry.write`.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals
open Solidity.Yul.Views

/-- **The Scalar pilot correspondence** of `geometry`, for every allocator. -/
theorem scalarPilot
    (a : Shrink.Params → Shrink.Layout → Shrink.Tree → Shrink.Phys → Option (Nat × Shrink.Phys)) :
    (Shrink.LayoutView.mk geometry a).ScalarPilot where
  scalar := (geometric a).scalar
  memoryScalar := (geometric a).memoryScalar
  scalarPathRead P _ _ f p c slot s r m hr := by
    have hread : geometry.scalar P f.width ⟨r, slot.val, f.offset⟩ m =
        some (f.findWord (m.slots r slot)).val := ((geometric a).scalar P r f slot m hr).1
    simp only [Shrink.Geometry.read, hread, Option.map_some, scalarPathView]
    cases s.read p with
    | none => simp only [Option.map_none, reduceCtorEq]
    | some v =>
      simp only [Option.map_some, Option.some.injEq, Shrink.Tree.leaf.injEq]
      exact ⟨congrArg Fin.val, Fin.ext⟩
  scalarPathWrite P _ _ f p c slot s r m hr := by
    have hwrite : ∀ v : f.Value, geometry.writeScalar P f.width ⟨r, slot.val, f.offset⟩ v.val m =
        some (m.withSlots r (patchScalarSlot (m.slots r) slot f v)) :=
      ((geometric a).scalar P r f slot m hr).2.1
    simp only [encodeScalarPath]
    cases s.read p with
    | none => rfl
    | some v =>
      have hw : 0 < f.width ∧ f.width ≤ 32 ∧ (c.encode v).val < 256 ^ f.width :=
        ⟨f.positive, by have := f.fits; omega, (c.encode v).isLt⟩
      simp only [Option.bind_some, Option.map_some, Shrink.Geometry.write, if_pos hw, hwrite]

end Solidity.Yul.Layout
