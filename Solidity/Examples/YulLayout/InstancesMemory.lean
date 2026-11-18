import Solidity.Yul.Layout.Instances.Memory

/-! Checks of the memory instance facts on small concrete inputs: each
declaration of `Yul/Layout/Instances/Memory.lean` is used once. -/
namespace Solidity.Examples.YulLayout.InstancesMemory

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout

/-- Two serialized words read back as a fixed array of two leaves. -/
example (P : Shrink.Params) (r : ByteView) (m : Shrink.Phys) :
    geometry.read P (.fixedArray (.scalar 32) 2) ⟨.memory, 128, 0⟩
        (m.withMemory (wordListView [7, 9] r 128)) = some (.node [.leaf 7, .leaf 9]) :=
  (Instances.wordList P [7, 9] r 128 m).1

/-- A byte past the two words is outside the footprint. -/
example (P : Shrink.Params) (r : ByteView) (m : Shrink.Phys) :
    ¬ geometry.cells P (.fixedArray (.scalar 32) 2) ⟨.memory, 128, 0⟩
        (m.withMemory (wordListView [7, 9] r 128)) (.mem 192) := fun inside =>
  absurd ((Instances.wordList P [7, 9] r 128 m).2 _ |>.mp inside)
    (show ¬ (128 ≤ 192 ∧ 192 < 128 + 2 * 32) by decide)

/-- An unsized member array is a dynamic array: its length word is in the footprint. -/
example (P : Shrink.Params) (r : ByteView) (m : Shrink.Phys) :
    geometry.cells P (.dynArray (.scalar 32)) ⟨.memory, 128, 0⟩
        (m.withMemory (memberArrayView none 1 (by decide) (fun _ => 5) r 128)) (.mem 128) :=
  (Instances.memberArray P none 1 (by decide) (fun _ => 5) r 128 m).2 _ |>.mpr
    (show 128 ≤ 128 ∧ 128 < 128 + (32 + 1 * 32) by decide)

/-- A sized member array is a fixed array of its words. -/
example (P : Shrink.Params) (r : ByteView) (m : Shrink.Phys) :
    geometry.read P (.fixedArray (.scalar 32) 1) ⟨.memory, 128, 0⟩
        (m.withMemory (memberArrayView (some 1) 1 (by decide) (fun _ => 5) r 128)) =
      some (.node [.leaf 5]) :=
  (Instances.memberArray P (some 1) 1 (by decide) (fun _ => 5) r 128 m).1

/-- A two-byte object reads back as its bytes. -/
example (P : Shrink.Params) (r : ByteView) (m : Shrink.Phys) :
    geometry.read P .bytes ⟨.memory, 128, 0⟩ (m.withMemory (bytesObjectView [1, 2] (by decide) r 128)) =
      some (.blob [1, 2]) :=
  (Instances.bytesObject P [1, 2] (by decide) r 128 m).1

/-- Two live objects of an enumerated heap have disjoint footprints. -/
example (P : Shrink.Params) {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (r image : ByteView) (m : Shrink.Phys) (view : enumeratedMemoryView p r = .ok image)
    (live : (h.cells 0).isSome ∧ (h.cells 1).isSome) :
    Shrink.Apart
      (geometry.cells P (Shrink.memoryShapeLayout (p.shape 0)) ⟨.memory, p.address 0, 0⟩
        (m.withMemory image))
      (geometry.cells P (Shrink.memoryShapeLayout (p.shape 1)) ⟨.memory, p.address 1, 0⟩
        (m.withMemory image)) :=
  (Instances.enumerated P p r image m view).2 0 1 live.1 live.2 (by decide)

end Solidity.Examples.YulLayout.InstancesMemory
