import Solidity.Backend.MemoryOps.CalldataRead
import Solidity.Backend.MemoryOps.DisjointOverwrite

/-!
# Inhabited decoded-object transport controls

The source record intentionally leaves byte decoding unspecified. These are
concrete typed decoded objects, not ABI-decoder or Source execution witnesses.
-/
namespace Solidity.Backend.MemoryOps.CalldataControls

private def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private def bs : List Bool := [true, false, true, false, true]
private def input (values : List Bool) : Source.Calldata D :=
  ⟨[1, 0, 1], fun off => if off = 7 then
    some ⟨.array .calldata .bool none, decodedBools values⟩ else none⟩
private theorem source_ok : DecodedBoolArray (input bs) 7 bs := rfl
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B, P]
private def dst : HRef H B := ⟨0, rfl⟩
private def parent : HRef H P := ⟨1, rfl⟩
private def heap : Heap H := (⟨[true, true, true, true, true], by decide⟩,
  ⟨[dst, dst], rfl⟩, ())
private theorem bounds : SliceBounds bs.length 1 4 := ⟨by decide, by decide⟩
private theorem space : 1 + ((bs.drop 1).take (4 - 1)).length ≤ heap.len dst .dyn := by
  simp only [Heap.len, MObj.elems_dyn]
  decide
private def out := overwriteSlice heap dst .dyn 1 ((bs.drop 1).take (4 - 1)) space

/-- Actual object reads feed changed destination cells; reference parent words
keep the same child identities, while the child contents really change. -/
theorem nonempty_transport :
    DecodedBoolRead (input bs) 7 1 false ∧
    MObj.elems .dyn (out.get dst) = [true, false, true, false, true] ∧
    (MObj.elems .fixed (out.get parent)).map HRef.id = [0, 0] := by
  refine ⟨decodedBoolArray_read source_ok 1 (by decide), ?_, ?_⟩
  · rw [out, overwriteSlice_elems]
    simp only [MObj.elems_dyn]
    rfl
  · rw [out, overwriteSlice_frame heap dst parent .dyn 1 _ space (by decide)]
    simp only [MObj.elems_fixed]
    rfl

/-- The coupled generic transport theorem is applied, not merely assumed. -/
theorem transport_application :
    ∃ b, (MObj.elems .dyn (out.get dst))[2]? = some b ∧
      DecodedBoolRead (input bs) 7 2 b ∧ out.get parent = heap.get parent :=
  decodedBoolSlice_transport source_ok heap dst parent .dyn 1 1 4 1 bounds space (by decide) (by decide)

theorem wrong_value : ¬ DecodedBoolRead (input bs) 7 1 true := by
  intro h
  have he := (decodedBoolRead_iff source_ok).mp h
  change some false = some true at he
  cases he

theorem endpoint_overrun : ¬ DecodedBoolRead (input bs) 7 5 false :=
  decodedBoolRead_overrun source_ok (by decide) false

theorem reversed_endpoint : ¬ SliceBounds bs.length 4 1 := reversed_invalid (by decide)

theorem absent_lookup : ¬ DecodedBoolArray (input bs) 8 bs := by
  intro h
  change (none : Option (Σ t, Source.Data D t)) = some _ at h
  cases h

private def wrong : Source.Calldata D :=
  ⟨[1], fun _ => some ⟨.bytes .calldata, .bytes [1]⟩⟩
theorem wrong_object_type : ¬ DecodedBoolArray wrong 7 bs := by
  intro h
  have hs := Option.some.inj h
  have ht := congrArg (fun x : Σ t, Source.Data D t => x.1) hs
  cases ht

theorem empty_source : ¬ DecodedBoolRead (input []) 7 0 false :=
  decodedBoolRead_overrun (show DecodedBoolArray (input []) 7 [] from rfl) (by decide) false

theorem empty_end_slice :
    ((bs.drop 5).take (5 - 5)).length = 0 ∧ SliceBounds bs.length 5 5 := by
  exact ⟨rfl, empty_at_end _⟩

private theorem end_space : 5 + ([] : List (MVal H (.prim .bool))).length ≤ heap.len dst .dyn := by
  simp only [Heap.len, MObj.elems_dyn]
  decide

/-- The empty captured slice at the source/destination end changes no heap object. -/
theorem empty_end_operation :
    overwriteSlice heap dst .dyn 5 ((bs.drop 5).take (5 - 5))
      (by simpa only [Nat.sub_self, List.take_zero] using end_space) = heap := by
  simpa only [Nat.sub_self, List.take_zero] using overwriteSlice_empty heap dst .dyn 5 end_space

private def boundaryBits : List Bool := (List.range 65).map (fun n => n == 32)
private def boundaryHeap : Heap H := (⟨List.replicate 65 false, by decide⟩,
  ⟨[dst, dst], rfl⟩, ())
private theorem boundarySpace :
    0 + ((boundaryBits.drop 31).take (64 - 31)).length ≤ boundaryHeap.len dst .dyn := by
  simp only [Heap.len, MObj.elems_dyn]
  decide
private def boundaryOut := overwriteSlice boundaryHeap dst .dyn 0
  ((boundaryBits.drop 31).take (64 - 31)) boundarySpace

/-- Source and destination cross index32 with nonempty data; exterior indices
and the actual source observation retain their values. These are element indices. -/
theorem boundary_transport :
    DecodedBoolRead (input boundaryBits) 7 32 true ∧
    (MObj.elems .dyn (boundaryOut.get dst))[1]? = some true ∧
    (MObj.elems .dyn (boundaryOut.get dst))[33]? = some false ∧
    (MObj.elems .dyn (boundaryOut.get dst))[64]? = some false := by
  constructor
  · exact decodedBoolArray_read (show DecodedBoolArray (input boundaryBits) 7 boundaryBits from rfl)
      32 (by decide)
  · rw [boundaryOut, overwriteSlice_elems]
    simp only [MObj.elems_dyn]
    decide

/-- info: 'Solidity.Backend.MemoryOps.CalldataControls.empty_end_operation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end_operation
/-- info: 'Solidity.Backend.MemoryOps.CalldataControls.nonempty_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nonempty_transport
/-- info: 'Solidity.Backend.MemoryOps.CalldataControls.transport_application' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms transport_application
/-- info: 'Solidity.Backend.MemoryOps.CalldataControls.wrong_value' depends on axioms: [propext] -/
#guard_msgs in #print axioms wrong_value
/-- info: 'Solidity.Backend.MemoryOps.CalldataControls.boundary_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms boundary_transport

end Solidity.Backend.MemoryOps.CalldataControls
