import Solidity.Yul.Layout.Instances.Storage

/-! Checks of the storage instance facts on small concrete inputs: each
declaration of `Yul/Layout/Instances/Storage.lean` is used once. -/
namespace Solidity.Examples.YulLayout.InstancesStorage

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout

/-- A scalar path at storage slot 5 is the recursive read of its field there. -/
example (P : Shrink.Params) {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (s : Source.Storage D L) (m : Shrink.Phys) :
    scalarPathView p c 5 s m.storage ↔
      (s.read p).map (fun v => Shrink.Tree.leaf (c.encode v).val) =
        geometry.read P (.scalar f.width) ⟨.storage, 5, f.offset⟩ m :=
  Instances.scalarPath P p c 5 s m

/-- Paths in different slots have disjoint footprints. -/
example (P : Shrink.Params) {D : Source.Layout} {L : Source.SPath → Source.STy}
    (c d : ScalarPath D L) (m : Shrink.Phys) (h : c.slot ≠ d.slot) :
    Shrink.Apart (geometry.cells P (.scalar c.field.width) ⟨.storage, c.slot.val, c.field.offset⟩ m)
      (geometry.cells P (.scalar d.field.width) ⟨.storage, d.slot.val, d.field.offset⟩ m) :=
  (Instances.apart P c d m).1 (Or.inl h)

/-- With no listed paths, every frame view holds. -/
example (P : Shrink.Params) {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (source : Source.EMState E Γ) (m : Shrink.Phys) :
    FiniteCellWrites.Views F [] [] source (m.storage, m.transient) :=
  (Instances.cells P F [] [] source m).2 ⟨nofun, nofun⟩

end Solidity.Examples.YulLayout.InstancesStorage
