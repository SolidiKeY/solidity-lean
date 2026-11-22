import Solidity.Yul.Layout.ScalarPilot
import Solidity.Yul.Views.FiniteCellWrites

/-!
# The storage instance facts of the layout view

The three storage fields of `Shrink.LayoutView.Instances`, for `geometry`:
`scalarPath`, `apart` and `cells`. Each statement is the field's, with
`geometry` for `V.geometry`; none mentions an allocator.

`scalarPath` and `cells` are `scalarPathRead` of `scalarPilot` (at `.storage`,
and at `.transient` for the transient paths of `cells`); `apart` reads the
scalar footprint off the `scalar` field of `geometric`.
-/
namespace Solidity.Yul.Layout.Instances

open Solidity.Goals
open Solidity.Yul.Views

/-- The pilot, at the allocator that never allocates (no field here reads it). -/
private theorem pilot : (Shrink.LayoutView.mk geometry fun _ _ _ _ => none).ScalarPilot :=
  scalarPilot fun _ _ _ _ => none

/-- `scalarPathView` over a slot region is the recursive read of the scalar. -/
private theorem pathRead (P : Shrink.Params) {D : Source.Layout} {L : Source.SPath → Source.STy}
    (c : ScalarPath D L) (s : Source.Storage D L) (r : Shrink.Region) (m : Shrink.Phys)
    (hr : r.slotted) :
    scalarPathView c.path c.codec c.slot s (m.slots r) ↔
      (s.read c.path).map (fun v => Shrink.Tree.leaf (c.codec.encode v).val) =
        geometry.read P (.scalar c.field.width) ⟨r, c.slot.val, c.field.offset⟩ m :=
  pilot.scalarPathRead P c.path c.codec c.slot s r m hr

/-- **`scalarPath`**: `scalarPathView` is the recursive view of the scalar in storage. -/
theorem scalarPath (P : Shrink.Params) {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : Shrink.Phys) :
    scalarPathView p c slot s m.storage ↔
      (s.read p).map (fun v => Shrink.Tree.leaf (c.encode v).val) =
        geometry.read P (.scalar f.width) ⟨.storage, slot.val, f.offset⟩ m :=
  pilot.scalarPathRead P p c slot s .storage m trivial

/-- The storage footprint of a scalar path: the bytes of its field in its slot. -/
private theorem scalar_cells (P : Shrink.Params) {D : Source.Layout}
    {L : Source.SPath → Source.STy} (c : ScalarPath D L) (m : Shrink.Phys) (x : Shrink.Cell) :
    geometry.cells P (.scalar c.field.width) ⟨.storage, c.slot.val, c.field.offset⟩ m x ↔
      ∃ b, x = .slot .storage c.slot b ∧ c.field.offset ≤ b ∧ b < c.field.offset + c.field.width :=
  by rw [Shrink.Geometry.cells]; exact (pilot.scalar P .storage c.field c.slot m trivial).2.2 x

/-- **`apart`**: `pathsApart` is disjointness of the storage footprints. -/
theorem apart (P : Shrink.Params) {D : Source.Layout} {L : Source.SPath → Source.STy}
    (c d : ScalarPath D L) (m : Shrink.Phys) :
    pathsApart c d ↔ Shrink.Apart (geometry.cells P (.scalar c.field.width)
        ⟨.storage, c.slot.val, c.field.offset⟩ m)
      (geometry.cells P (.scalar d.field.width) ⟨.storage, d.slot.val, d.field.offset⟩ m) := by
  constructor
  · intro h x ⟨hc, hd⟩
    obtain ⟨b, rfl, hb1, hb2⟩ := (scalar_cells P c m x).1 hc
    obtain ⟨b', he, hb1', hb2'⟩ := (scalar_cells P d m _).1 hd
    simp only [Shrink.Cell.slot.injEq, true_and] at he
    obtain ⟨hs, rfl⟩ := he
    rcases h with h | h | h
    · exact h hs
    · omega
    · omega
  · intro h
    refine Classical.byContradiction fun hn => ?_
    simp only [pathsApart, not_or, Classical.not_not] at hn
    obtain ⟨hs, h1, h2⟩ := hn
    have hcw := c.field.positive
    have hdw := d.field.positive
    let b := max c.field.offset d.field.offset
    refine h (.slot .storage c.slot b) ⟨(scalar_cells P c m _).2 ⟨b, rfl, ?_, ?_⟩,
      (scalar_cells P d m _).2 ⟨b, by rw [hs], ?_, ?_⟩⟩ <;> omega

/-- **`cells`**: `FiniteCellWrites.Views` is the recursive view of every listed
persistent path in storage and every listed transient path in transient storage. -/
theorem cells (P : Shrink.Params) {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (source : Source.EMState E Γ)
    (m : Shrink.Phys) :
    FiniteCellWrites.Views F ps ts source (m.storage, m.transient) ↔
      (∀ c ∈ ps, ((source.2.ex.world.accounts F.this).storage.read c.path).map
          (fun v => Shrink.Tree.leaf (c.codec.encode v).val) =
        geometry.read P (.scalar c.field.width) ⟨.storage, c.slot.val, c.field.offset⟩ m) ∧
      (∀ c ∈ ts, ((source.2.ex.transient.cells F.this).read c.path).map
          (fun v => Shrink.Tree.leaf (c.codec.encode v).val) =
        geometry.read P (.scalar c.field.width) ⟨.transient, c.slot.val, c.field.offset⟩ m) :=
  and_congr
    (forall_congr' fun c => imp_congr_right fun _ => pathRead P c _ .storage m trivial)
    (forall_congr' fun c => imp_congr_right fun _ => pathRead P c _ .transient m trivial)

end Solidity.Yul.Layout.Instances
