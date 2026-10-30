import Solidity.Backend.MemoryOps.CalldataTransport
import Solidity.Backend.MemoryOps.CalldataRead

/-! An actual initial decoded-reference/typed-heap correspondence discharges
the generic transport premise. Both child table lookups have contents matching
the heap; no decoder, constructor, deep copy or child execution is introduced. -/
namespace Solidity.Backend.MemoryOps.TransportControls
private def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private abbrev T : Source.STy := .array .calldata .bool none
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B, B, P]
private def first : HRef H B := ⟨0, rfl⟩
private def second : HRef H B := ⟨1, rfl⟩
private def parent : HRef H P := ⟨2, rfl⟩
private def hp : Heap H := (⟨[true], by decide⟩, ⟨[false], by decide⟩, ⟨[first, first], rfl⟩, ())
private def ref (off : Nat) : Source.Data D T := .val (.cdRef rfl off)
private def xs (j : Fin 2) : Source.Data D T := if j.val = 0 then ref 42 else ref 37
private theorem hn : ∀ m, (none : Option Nat) = some m → m = 2 := by intro m h; cases h
private def c : Source.Calldata D := ⟨[], fun off =>
  if off = 7 then some ⟨.array .calldata T none, .array 2 hn xs⟩ else
  if off = 37 then some ⟨T, decodedBools [true]⟩ else
  if off = 42 then some ⟨T, decodedBools [false]⟩ else none⟩
private theorem lookup : DecodedArrayAt c 7 2 hn xs := rfl
private def address (i : Nat) := if i = 0 then 37 else 42
/-- Initial correspondence includes actual child contents, not just a freely
chosen relation between source and destination observations. -/
private def Rep (input : Source.Calldata D) (h : Heap H)
    (s : Source.Data D T) (r : HRef H B) : Prop :=
  s = ref (address r.id) ∧ input.objects (address r.id) =
    some ⟨T, decodedBools (MObj.elems .dyn (h.get r))⟩
private def values : List (MVal H (.ref B)) := [second, first]
private theorem initial_elements (j : Fin 2) : Rep c hp (xs j) (values[j.val]'j.isLt) := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero => constructor; rfl; simp only [MObj.elems_dyn]; rfl
  | succ j => cases j with
    | zero => constructor; rfl; simp only [MObj.elems_dyn]; rfl
    | succ j => omega
private theorem space : 0 + ((values.drop 0).take (2 - 0)).length ≤ hp.len parent .fixed := by
  simp only [Heap.len, MObj.elems_fixed]; decide
private def out := overwriteSlice hp parent .fixed 0 ((values.drop 0).take (2 - 0)) space

/-- Discharges lookup, runtime capacities and all element-representation premises
of actual generic nonprimitive slice transport. -/
theorem generic_application :
    ∃ s v, DecodedArrayRead c 7 T none 0 s ∧
      (MObj.elems .fixed (out.get parent))[0]? = some v ∧
      Rep c hp s v ∧ out.get first = hp.get first :=
  decodedArray_overwrite_transport lookup hp parent first .fixed values rfl
    (Rep c hp) initial_elements 0 0 2 0 ⟨by decide, by decide⟩ space (by decide) (by decide)

/-- The parent redirects to the actual second child, whose immutable decoded
contents and final heap contents still agree; pointer identity is explicit. -/
theorem reference_contents :
    (MObj.elems .fixed (out.get parent)).map HRef.id = [1, 0] ∧
    Rep c out (ref 42) second ∧ Rep c out (ref 37) first := by
  refine ⟨?_, ?_, ?_⟩
  · rw [out, overwriteSlice_elems]
    simp only [MObj.elems_fixed]; rfl
  · constructor
    · rfl
    · rw [out, overwriteSlice_frame hp parent second .fixed 0 _ space (by decide)]
      simp only [MObj.elems_dyn]; rfl
  · constructor
    · rfl
    · rw [out, overwriteSlice_frame hp parent first .fixed 0 _ space (by decide)]
      simp only [MObj.elems_dyn]; rfl

/-- A different source offset cannot be represented by the same typed child. -/
theorem wrong_child_identity : ¬ Rep c hp (ref 37) second := by
  intro h
  have hv := h.1
  change ref 37 = ref 42 at hv
  cases hv
private def missing : Source.Calldata D := ⟨[], fun off =>
  if off = 7 then some ⟨.array .calldata T none, .array 2 hn xs⟩ else none⟩
/-- A table containing the parent alone does not supply child correspondence. -/
theorem missing_child_negative : ¬ Rep missing hp (ref 42) second := by
  intro h
  have ho := h.2
  change none = some _ at ho
  cases ho

/-- info: 'Solidity.Backend.MemoryOps.TransportControls.generic_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generic_application
/-- info: 'Solidity.Backend.MemoryOps.TransportControls.reference_contents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reference_contents
/-- info: 'Solidity.Backend.MemoryOps.TransportControls.wrong_child_identity' depends on axioms: [propext] -/
#guard_msgs in #print axioms wrong_child_identity
/-- info: 'Solidity.Backend.MemoryOps.TransportControls.missing_child_negative' depends on axioms: [propext] -/
#guard_msgs in #print axioms missing_child_negative
end Solidity.Backend.MemoryOps.TransportControls
