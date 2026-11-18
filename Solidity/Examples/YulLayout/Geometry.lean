import Solidity.Yul.Layout.Geometric

/-! Checks of the layout geometry on small concrete inputs: each declaration
of `Yul/Layout/Geometry.lean` and `Yul/Layout/Geometric.lean` is used once. -/
namespace Solidity.Examples.YulLayout.Geometry

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout

/-- The all-zero machine. -/
private def zero : Shrink.Phys := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- A field that fits its slot is kept; one that does not moves to offset 0. -/
example : (slotField 4 28).map (·.offset) = some 28 := rfl
example : (slotField 4 30).map (·.offset) = some 0 := rfl
example : (slotField 33 0).isNone := rfl

/-- A word, a two-word header and three words. -/
example : memSize (.struct [.scalar 1, .dynArray .bytes, .fixedArray (.scalar 32) 3]) = 192 := rfl
example : memSizes [.scalar 1, .bytes] = 96 := rfl
example : memberOffset [.scalar 1, .dynArray .bytes, .scalar 32] 2 = 96 := rfl
example : indirect .bytes = 1 ∧ indirect (.scalar 32) = 0 := ⟨rfl, rfl⟩

/-- Memory data follows the length word, or the address of an indirect header. -/
example (P : Shrink.Params) (m : Shrink.Phys) :
    dataLoc P ⟨.memory, 128, 0⟩ m = ⟨.memory, 160, 0⟩ := rfl
example (P : Shrink.Params) (m : Shrink.Phys) :
    dataLoc P ⟨.memory, 128, 1⟩ m = ⟨.memory, mloadNat m.memory 160, 0⟩ := rfl

/-- The first byte of slot data is the most significant byte of its slot. -/
example : readSlotBytes (fun _ => Shrink.toWord (5 * 256 ^ 31)) 9 1 = [5] := by decide
example : readSlotBytes (writeSlotBytes 9 [5, 6] 0 (fun _ => 0)) 9 2 = [5, 6] := by decide

/-- A nested `bytes` element is a two-word header, marked indirect. -/
example (P : Shrink.Params) :
    geometry.elem P .bytes ⟨.memory, 128, 0⟩ 2 = ⟨.memory, 256, 1⟩ := rfl

/-- The view reads the empty `bytes` object from zero memory. -/
example (P : Shrink.Params) :
    geometry.read P .bytes ⟨.memory, 128, 0⟩ zero = some (.blob []) := by
  rw [Shrink.Geometry.read]
  rfl

/-- A length write through an indirect header is refused. -/
example (P : Shrink.Params) (m : Shrink.Phys) :
    geometry.writeLength P ⟨.memory, 128, 1⟩ 0 m = none := rfl

/-- A packed storage scalar reads back what was written, by `geometric`. -/
example (P : Shrink.Params) (f : Field) (slot : Roadmap.Word) (m : Shrink.Phys) (v : f.Value) :
    (geometry.writeScalar P f.width ⟨.storage, slot.val, f.offset⟩ v.val m).bind
      (geometry.scalar P f.width ⟨.storage, slot.val, f.offset⟩) = some v.val := by
  have g := geometric (fun _ _ _ _ => none)
  rw [(g.scalar P .storage f slot m trivial).2.1 v, Option.bind_some,
    (g.scalar P .storage f slot _ trivial).1]
  exact congrArg (fun x : f.Value => some x.val) (patchScalarSlot_find ..)

end Solidity.Examples.YulLayout.Geometry
