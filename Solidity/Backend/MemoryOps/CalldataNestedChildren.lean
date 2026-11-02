import Solidity.Backend.MemoryOps.CalldataChildren

/-! Compose existing typed child-table observations for reference-containing
children. This explicit nested clause is not a recursive graph-copy semantics
or a depth admission bound; arbitrary recursive correspondence remains open. -/
namespace Solidity.Backend.MemoryOps
abbrev RefChildTy : Source.STy := .array .calldata BoolChildTy none
abbrev RefChildRef : RefTy := .array (.ref BoolChildRef)

/-- Representation of already-existing reference elements as decoded pointers;
not a payload converter, target emitter or decoder. -/
def decodedChildRefs {D : Source.Layout} {H : HTy} (address : Nat → Nat)
    (rs : List (HRef H BoolChildRef)) : Source.Data D RefChildTy :=
  .array rs.length (fun _ h => by cases h)
    (fun j => .val (.cdRef rfl (address rs[j].id)))

/-- Both the reference-containing child's table and its actual Boolean children
are represented, with identities retained at each edge. -/
def RefChildRepr {D : Source.Layout} {H : HTy} (c : Source.Calldata D)
    (address : Nat → Nat) (hp : Heap H) (s : Source.Data D RefChildTy)
    (r : HRef H RefChildRef) : Prop :=
  s = .val (.cdRef rfl (address r.id)) ∧
  c.objects (address r.id) = some ⟨RefChildTy, decodedChildRefs address (MObj.elems .dyn (hp.get r))⟩ ∧
  ∀ q ∈ MObj.elems .dyn (hp.get r),
    BoolChildRepr c address hp (.val (.cdRef rfl (address q.id))) q

/-- Actual framing of the child and each referenced descendant yields the
nested correspondence at the output heap. Repeated descendants are allowed. -/
theorem RefChildRepr.overwrite {D : Source.Layout} {H : HTy} {R : RefTy} {E : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (dst : HRef H R) (a : ArrTy R E)
    (offset : Nat) (payload : List (MVal H E))
    (hd : offset + payload.length ≤ hp.len dst a) (hroot : dst.id ≠ r.id)
    (hleaf : ∀ q ∈ MObj.elems .dyn (hp.get r), dst.id ≠ q.id) :
    RefChildRepr c address (overwriteSlice hp dst a offset payload hd) s r := by
  refine ⟨hr.1, ?_, ?_⟩
  · rw [overwriteSlice_frame hp dst r a offset payload hd hroot]
    exact hr.2.1
  · intro q hq
    rw [overwriteSlice_frame hp dst r a offset payload hd hroot] at hq
    exact (hr.2.2 q hq).overwrite dst a offset payload hd (hleaf q hq)

/-- A published typed memory index and the immutable decoded child read select
the same reference identity, whose own contents are represented at this heap. -/
theorem RefChildRepr.index {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (i : PrimTy.uint.Denote)
    (hi : i.1.toNat < hp.len r .dyn) :
    ∃ q, hp.index r .dyn i = some q ∧
      DecodedArrayRead c (address r.id) BoolChildTy none i.1.toNat
        (.val (.cdRef rfl (address q.id))) ∧
      BoolChildRepr c address hp (.val (.cdRef rfl (address q.id))) q := by
  let rs := MObj.elems .dyn (hp.get r)
  have hq : rs[i.1.toNat]? = some rs[i.1.toNat] := List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  refine ⟨rs[i.1.toNat], hq, ?_, hr.2.2 _ (List.getElem_mem hi)⟩
  exact ⟨rs.length, (fun j => .val (.cdRef rfl (address rs[j].id))), hi,
    (fun _ h => by cases h), hr.2.1, rfl⟩

/-- The actual typed child index rejects an endpoint overrun, and no finite
decoded child observation can witness that index. No Source halt is invented. -/
theorem RefChildRepr.index_bounds {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (i : PrimTy.uint.Denote)
    (hi : hp.len r .dyn ≤ i.1.toNat) (v : Source.Data D BoolChildTy) :
    hp.index r .dyn i = none ∧ ¬ DecodedArrayRead c (address r.id) BoolChildTy none i.1.toNat v := by
  refine ⟨List.getElem?_eq_none_iff.mpr hi, ?_⟩
  have hc : DecodedArrayAt (τ := BoolChildTy) (n := none) c (address r.id) (MObj.elems .dyn (hp.get r)).length
      (fun _ h => by cases h)
      (fun j => .val (.cdRef rfl (address (MObj.elems .dyn (hp.get r))[j].id))) := hr.2.1
  exact decodedArrayRead_overrun hc hi v

/-- Compose two real typed memory-index observations with decoded child reads.
This does not evaluate a replacement interpreter or assume path preservation. -/
theorem RefChildRepr.index_bool {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (i : PrimTy.uint.Denote)
    (hi : i.1.toNat < hp.len r .dyn) (j : PrimTy.uint.Denote) (b : Bool) :
    ∃ q, hp.index r .dyn i = some q ∧
      DecodedArrayRead c (address r.id) BoolChildTy none i.1.toNat
        (.val (.cdRef rfl (address q.id))) ∧
      (DecodedBoolRead c (address q.id) j.1.toNat b ↔ hp.index q .dyn j = some b) := by
  obtain ⟨q, hq, hs, hc⟩ := hr.index i hi
  exact ⟨q, hq, hs, hc.read_iff _ b⟩

/-- These specialized finite shapes derive both levels of separation. -/
theorem refChild_parent_ne {H : HTy} {R : RefTy} (dst : HRef H R)
    (a : ArrTy R (.ref RefChildRef)) (q : HRef H RefChildRef) : dst.id ≠ q.id := by
  intro he
  have ht := (HRef.heq_of_id dst q he).1
  cases a <;> cases ht

theorem refChild_leaf_ne {H : HTy} {R : RefTy} (dst : HRef H R)
    (a : ArrTy R (.ref RefChildRef)) (q : HRef H BoolChildRef) : dst.id ≠ q.id := by
  intro he
  have ht := (HRef.heq_of_id dst q he).1
  cases a <;> cases ht

/-- Arbitrary runtime slices of reference-containing children have nested
correspondence at the output heap. Both footprint levels are separate by
intrinsic typing. No pairwise separation among children is needed. -/
theorem decodedRefChildren_overwrite {D : Source.Layout} {H : HTy} {R : RefTy}
    {c : Source.Calldata D} {address : Nat → Nat} {n : Option Nat} {off len : Nat}
    {hn : ∀ m, n = some m → m = len} {xs : Fin len → Source.Data D RefChildTy}
    (hc : DecodedArrayAt c off len hn xs) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.ref RefChildRef)) (values : List (HRef H RefChildRef))
    (hl : values.length = len)
    (hr : ∀ j : Fin len, RefChildRepr c address hp (xs j) (values[j.val]'(hl ▸ j.isLt)))
    (offset start stop : Nat) (hb : SliceBounds len start stop)
    (hd : offset + ((values.drop start).take (stop - start)).length ≤ hp.len dst a)
    (i : Nat) (hi : i < stop - start) :
    let j : Fin len := ⟨start + i, hb.index hi⟩
    let r := values[j.val]'(hl ▸ j.isLt)
    let out := overwriteSlice hp dst a offset ((values.drop start).take (stop - start)) hd
    DecodedArrayRead c off RefChildTy n (start + i) (xs j) ∧
      (MObj.elems a (out.get dst))[offset + i]? = some r ∧ RefChildRepr c address out (xs j) r := by
  dsimp only
  have hv : SliceBounds values.length start stop := by rw [hl]; exact hb
  refine ⟨(decodedArrayRead_iff hc _).mpr ⟨hb.index hi, rfl⟩, ?_, ?_⟩
  · rw [overwriteSlice_inside]
    · rw [SliceBounds.read hi]
      exact List.getElem?_eq_some_iff.mpr ⟨hv.index hi, rfl⟩
    · rw [hv.length]; exact hi
  · exact (hr ⟨start + i, hb.index hi⟩).overwrite dst a offset _ hd
      (refChild_parent_ne dst a _)
      (fun q _ => refChild_leaf_ne dst a q)

/-- info: 'Solidity.Backend.MemoryOps.refChild_parent_ne' does not depend on any axioms -/
#guard_msgs in #print axioms refChild_parent_ne
/-- info: 'Solidity.Backend.MemoryOps.refChild_leaf_ne' does not depend on any axioms -/
#guard_msgs in #print axioms refChild_leaf_ne
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.overwrite
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.index' depends on axioms: [propext] -/
#guard_msgs in #print axioms RefChildRepr.index
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.index_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.index_bounds
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.index_bool' depends on axioms: [propext] -/
#guard_msgs in #print axioms RefChildRepr.index_bool
/-- info: 'Solidity.Backend.MemoryOps.decodedRefChildren_overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedRefChildren_overwrite
end Solidity.Backend.MemoryOps
