import Solidity.Backend.MemoryOps.CalldataChildExtension

/-! A changed parent selects a reference-containing child with repeated leaf
aliases. Initial and final child tables and both typed index observations agree. -/
namespace Solidity.Backend.MemoryOps.NestedChildControls
private def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private abbrev B := BoolChildRef
private abbrev C := RefChildRef
private abbrev P : RefTy := .array (.ref C)
private abbrev H : HTy := [B, B, C, C, P]
private def first : HRef H B := ⟨0, rfl⟩
private def second : HRef H B := ⟨1, rfl⟩
private def childA : HRef H C := ⟨2, rfl⟩
private def childB : HRef H C := ⟨3, rfl⟩
private def parent : HRef H P := ⟨4, rfl⟩
private def hp : Heap H := (⟨[true], by decide⟩, ⟨[false], by decide⟩,
  ⟨[first, second, first], by decide⟩, ⟨[second, second], by decide⟩,
  ⟨[childA, childA], by decide⟩, ())
private def address (i : Nat) := if i = 0 then 37 else if i = 1 then 42 else if i = 2 then 70 else 80
private def sourceRef (off : Nat) : Source.Data D RefChildTy := .val (.cdRef rfl off)
private def xs (j : Fin 2) : Source.Data D RefChildTy := if j.val = 0 then sourceRef 80 else sourceRef 70
private theorem hn : ∀ m, (none : Option Nat) = some m → m = 2 := by intro m h; cases h
private def input : Source.Calldata D := ⟨[], fun off =>
  if off = 7 then some ⟨.array .calldata RefChildTy none, .array 2 hn xs⟩ else
  if off = 37 then some ⟨BoolChildTy, decodedBools [true]⟩ else
  if off = 42 then some ⟨BoolChildTy, decodedBools [false]⟩ else
  if off = 70 then some ⟨RefChildTy, decodedChildRefs address [first, second, first]⟩ else
  if off = 80 then some ⟨RefChildTy, decodedChildRefs address [second, second]⟩ else none⟩
private theorem lookup : DecodedArrayAt input 7 2 hn xs := rfl
private theorem refs (r : HRef H B) : r = first ∨ r = second := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact .inl rfl
  | succ i => cases i with
    | zero => cases hi; exact .inr rfl
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases i with
        | zero => cases hi
        | succ i => cases i with
          | zero => cases hi
          | succ i => cases hi
private theorem leaves (r : HRef H B) : BoolChildRepr input address hp
    (.val (.cdRef rfl (address r.id))) r := by
  rcases refs r with rfl | rfl <;> constructor
  all_goals first | rfl | simp only [MObj.elems_dyn]; rfl
private theorem initialA : RefChildRepr input address hp (sourceRef 70) childA := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · intro q _; exact leaves q
private theorem initialB : RefChildRepr input address hp (sourceRef 80) childB := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · intro q _; exact leaves q
private def values : List (HRef H C) := [childB, childA]
private theorem initial (j : Fin 2) : RefChildRepr input address hp (xs j) (values[j.val]'j.isLt) := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero => exact initialB
  | succ j => cases j with
    | zero => exact initialA
    | succ j => omega
private theorem space : 0 + ((values.drop 0).take (2 - 0)).length ≤ hp.len parent .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
private def out := overwriteSlice hp parent .dyn 0 ((values.drop 0).take (2 - 0)) space

/-- The general nested slice theorem supplies the actual output relation. -/
theorem final_child : RefChildRepr input address out (sourceRef 80) childB := by
  have h := decodedRefChildren_overwrite lookup hp parent .dyn values rfl initial
    0 0 2 ⟨by decide, by decide⟩ space
    0 (by decide)
  exact h.2.2

/-- Nonempty parent references change while nested shared leaves stay shared. -/
theorem changed_nested :
    (MObj.elems .dyn (hp.get parent)).map HRef.id = [2, 2] ∧
    (MObj.elems .dyn (out.get parent)).map HRef.id = [3, 2] ∧
    (MObj.elems .dyn (out.get childB)).map HRef.id = [1, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · rw [out, overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · rw [out, overwriteSlice_frame hp parent childB .dyn 0 _ space (by decide)]
    simp only [MObj.elems_dyn]; rfl
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
/-- Compose the published typed child index and Boolean leaf observation. -/
theorem nested_observation : ∃ q,
    out.index childB .dyn zero = some q ∧
    DecodedArrayRead input 80 BoolChildTy none 0 (.val (.cdRef rfl (address q.id))) ∧
    (DecodedBoolRead input (address q.id) 0 false ↔ out.index q .dyn zero = some false) := by
  apply final_child.index_bool zero _ zero false
  simp only [Heap.len, out, overwriteSlice_frame hp parent childB .dyn 0 _ space (by decide), MObj.elems_dyn]
  decide

/-- Both actual final memory-index observations yield the represented false leaf. -/
theorem actual_nested_read : out.index childB .dyn zero = some second ∧
    out.index second .dyn zero = some false ∧ DecodedBoolRead input 42 0 false := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Heap.index, out, overwriteSlice_frame hp parent childB .dyn 0 _ space (by decide), MObj.elems_dyn]
    rfl
  · simp only [Heap.index, out, overwriteSlice_frame hp parent second .dyn 0 _ space (by decide), MObj.elems_dyn]
    rfl
  · exact decodedBoolArray_read (show DecodedBoolArray input 42 [false] from rfl) 0 (by decide)

private def two : PrimTy.uint.Denote := ⟨2, by decide⟩
/-- Exact-end failure is observed by the existing typed index and decoded table. -/
theorem nested_bounds : out.index childB .dyn two = none ∧
    ¬ DecodedArrayRead input 80 BoolChildTy none 2 (.val (.cdRef rfl 42)) := by
  apply final_child.index_bounds two _ _
  simp only [Heap.len, out, overwriteSlice_frame hp parent childB .dyn 0 _ space (by decide), MObj.elems_dyn]
  decide
/-- info: 'Solidity.Backend.MemoryOps.NestedChildControls.nested_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_bounds

private def extensionObject : MObj H C := ⟨[first, second], by decide⟩
/-- Actual allocation preserves the represented nested child's full observed
footprint, and its identity is distinct from the newly allocated same-type root. -/
theorem nested_allocation :
    RefChildRepr input address (out.alloc extensionObject).1 (sourceRef 80)
      (childB.wk (List.prefix_append H [C])) ∧
    (childB.wk (List.prefix_append H [C])).id ≠ (out.alloc extensionObject).2.id :=
  ⟨final_child.grow _ (Heap.keeps_alloc _ _), old_ne_fresh out extensionObject childB⟩
/-- info: 'Solidity.Backend.MemoryOps.NestedChildControls.nested_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_allocation

/-- info: 'Solidity.Backend.MemoryOps.NestedChildControls.final_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms final_child
/-- info: 'Solidity.Backend.MemoryOps.NestedChildControls.changed_nested' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_nested
/-- info: 'Solidity.Backend.MemoryOps.NestedChildControls.nested_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_observation
/-- info: 'Solidity.Backend.MemoryOps.NestedChildControls.actual_nested_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_nested_read
end Solidity.Backend.MemoryOps.NestedChildControls
