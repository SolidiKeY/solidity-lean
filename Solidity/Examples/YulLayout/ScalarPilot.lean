import Solidity.Yul.Layout.ScalarPilot

/-! Checks of `Yul/Layout/ScalarPilot.lean` on small inputs: `scalarPilot`
is used in both slot regions and in memory. -/
namespace Solidity.Examples.YulLayout.ScalarPilot

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout

/-- The pilot for the allocator that refuses every allocation. -/
private theorem pilot : (Shrink.LayoutView.mk geometry (fun _ _ _ _ => none)).ScalarPilot :=
  scalarPilot _

/-- A transient path reads as the view of its slot. -/
example (P : Shrink.Params) {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (s : Source.Storage D L) (m : Shrink.Phys) :
    scalarPathView p c 7 s m.transient ↔
      (s.read p).map (fun v => Shrink.Tree.leaf (c.encode v).val) =
        geometry.read P (.scalar f.width) ⟨.transient, 7, f.offset⟩ m :=
  pilot.scalarPathRead P p c 7 s .transient m trivial

/-- A storage path writes as `encodeScalarPath` at slot 3. -/
example (P : Shrink.Params) {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (s : Source.Storage D L) (m : Shrink.Phys) :
    (s.read p).bind (fun v =>
        geometry.write P (.scalar f.width) ⟨.storage, 3, f.offset⟩ (.leaf (c.encode v).val) m) =
      (encodeScalarPath p c 3 s m.storage).map m.withStorage :=
  pilot.scalarPathWrite P p c 3 s .storage m trivial

/-- A full memory word at address 64 reads as `mload` without cleaning. -/
example (m : Shrink.Phys) (P : Shrink.Params) (h : P.cleanDirty = false) :
    geometry.scalar P 32 ⟨.memory, 64, 0⟩ m = some (mloadNat m.memory 64) := by
  rw [(pilot.memoryScalar P 32 64 m (by decide) (by decide)).1, h]
  rfl

/-- A one-byte field at offset 31 of storage slot 0 covers byte 31 only. -/
example (P : Shrink.Params) (m : Shrink.Phys) :
    geometry.scalarCells P 1 ⟨.storage, 0, 31⟩ (.slot .storage 0 31) :=
  ((pilot.scalar P .storage ⟨31, 1, by decide, by decide⟩ 0 m trivial).2.2 _).2 ⟨31, rfl, by decide, by decide⟩

end Solidity.Examples.YulLayout.ScalarPilot
