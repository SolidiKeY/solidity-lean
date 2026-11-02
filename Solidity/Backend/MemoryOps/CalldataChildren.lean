import Solidity.Backend.MemoryOps.CalldataTransport
import Solidity.Backend.MemoryOps.CalldataRead
import Solidity.Backend.MemoryOps.DisjointOverwrite

/-! Actual decoded child correspondence at the output heap. Separation is a
local framing hypothesis, never an admission restriction. The aliased-write
case is deliberately not inferred from initial correspondence. -/
namespace Solidity.Backend.MemoryOps

abbrev BoolChildTy : Source.STy := .array .calldata .bool none
abbrev BoolChildRef : RefTy := .array (.prim .bool)

/-- An existing source pointer and its immutable child-table contents correspond
to an actual typed heap child. No compiler or preservation relation occurs. -/
def BoolChildRepr {D : Source.Layout} {H : HTy} (c : Source.Calldata D)
    (address : Nat → Nat) (hp : Heap H) (s : Source.Data D BoolChildTy)
    (r : HRef H BoolChildRef) : Prop :=
  s = .val (.cdRef rfl (address r.id) 0) ∧
  c.objects (address r.id) = some ⟨BoolChildTy, decodedBools (MObj.elems .dyn (hp.get r))⟩

/-- Derive output correspondence from the actual other-object frame theorem. -/
theorem BoolChildRepr.overwrite {D : Source.Layout} {H : HTy} {R : RefTy} {E : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (dst : HRef H R) (a : ArrTy R E)
    (offset : Nat) (payload : List (MVal H E))
    (hd : offset + payload.length ≤ hp.len dst a) (hne : dst.id ≠ r.id) :
    BoolChildRepr c address (overwriteSlice hp dst a offset payload hd) s r := by
  refine ⟨hr.1, ?_⟩
  rw [overwriteSlice_frame hp dst r a offset payload hd hne]
  exact hr.2

/-- Correspondence gives exact published finite decoded reads at this heap,
not merely a relation closed over an earlier heap. -/
theorem BoolChildRepr.read_iff {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (i : Nat) (b : Bool) :
    DecodedBoolRead c (address r.id) i b ↔ (MObj.elems .dyn (hp.get r))[i]? = some b :=
  decodedBoolRead_iff hr.2

/-- Repeated typed child identities retain repeated source pointer identities. -/
theorem BoolChildRepr.alias {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s t : Source.Data D BoolChildTy} {r q : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (hq : BoolChildRepr c address hp t q)
    (he : r.id = q.id) : s = t := by
  rw [hr.1, hq.1, he]

/-- Reverse pointer identity requires an initial injective address assignment. -/
theorem BoolChildRepr.alias_iff {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s t : Source.Data D BoolChildTy} {r q : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (hq : BoolChildRepr c address hp t q)
    (hinj : ∀ (u v : HRef H BoolChildRef), address u.id = address v.id → u.id = v.id) :
    s = t ↔ r.id = q.id := by
  constructor
  · intro he
    have hs := hr.1.symm.trans (he.trans hq.1)
    have ha : address r.id = address q.id := by
      injection hs with ht hv
      injection hv with ht ha
    exact hinj r q ha
  · exact hr.alias hq

/-- The finite intrinsic parent/Boolean-child shapes already force separation. -/
theorem boolChild_parent_ne {H : HTy} {R : RefTy} (dst : HRef H R)
    (a : ArrTy R (.ref BoolChildRef)) (q : HRef H BoolChildRef) : dst.id ≠ q.id := by
  intro he
  have ht := (HRef.heq_of_id dst q he).1
  cases a <;> cases ht

/-- Arbitrary runtime reference slices have correspondence at the actual
output heap. Intrinsic types derive destination/child separation; children
may alias one another and no length/depth cutoff is imposed. -/
theorem decodedBoolChildren_overwrite {D : Source.Layout} {H : HTy} {R : RefTy}
    {c : Source.Calldata D} {address : Nat → Nat} {n : Option Nat} {off len : Nat}
    {hn : ∀ m, n = some m → m = len} {xs : Fin len → Source.Data D BoolChildTy}
    (hc : DecodedArrayAt c off len hn xs) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.ref BoolChildRef)) (values : List (HRef H BoolChildRef))
    (hl : values.length = len)
    (hr : ∀ j : Fin len, BoolChildRepr c address hp (xs j) (values[j.val]'(hl ▸ j.isLt)))
    (offset start stop : Nat) (hb : SliceBounds len start stop)
    (hd : offset + ((values.drop start).take (stop - start)).length ≤ hp.len dst a)
    (i : Nat) (hi : i < stop - start) :
    let j : Fin len := ⟨start + i, hb.index hi⟩
    let r := values[j.val]'(hl ▸ j.isLt)
    let out := overwriteSlice hp dst a offset ((values.drop start).take (stop - start)) hd
    DecodedArrayRead c off BoolChildTy n (start + i) (xs j) ∧
      (MObj.elems a (out.get dst))[offset + i]? = some r ∧ BoolChildRepr c address out (xs j) r := by
  dsimp only
  have hv : SliceBounds values.length start stop := by rw [hl]; exact hb
  refine ⟨(decodedArrayRead_iff hc _).mpr ⟨hb.index hi, rfl⟩, ?_, ?_⟩
  · rw [overwriteSlice_inside]
    · rw [SliceBounds.read hi]
      exact List.getElem?_eq_some_iff.mpr ⟨hv.index hi, rfl⟩
    · rw [hv.length]; exact hi
  · exact (hr ⟨start + i, hb.index hi⟩).overwrite dst a offset _ hd
      (boolChild_parent_ne dst a _)

/-- Empty and exact-end captures change no object; no child-separation premise
is needed when there is no selected child. -/
theorem referenceSlice_empty {H : HTy} {R Q : RefTy} (hp : Heap H)
    (dst : HRef H R) (a : ArrTy R (.ref Q)) (values : List (HRef H Q))
    (offset start : Nat) (hd : offset ≤ hp.len dst a) :
    overwriteSlice hp dst a offset ((values.drop start).take (start - start))
      (by simpa only [Nat.sub_self, List.take_zero, List.length_nil, Nat.add_zero] using hd) = hp := by
  simpa only [Nat.sub_self, List.take_zero] using
    overwriteSlice_empty hp dst a offset (by simpa only [List.length_nil, Nat.add_zero] using hd)

/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.overwrite
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.read_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms BoolChildRepr.read_iff
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.alias_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms BoolChildRepr.alias_iff
/-- info: 'Solidity.Backend.MemoryOps.boolChild_parent_ne' does not depend on any axioms -/
#guard_msgs in #print axioms boolChild_parent_ne
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.alias' depends on axioms: [propext] -/
#guard_msgs in #print axioms BoolChildRepr.alias
/-- info: 'Solidity.Backend.MemoryOps.decodedBoolChildren_overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedBoolChildren_overwrite
/-- info: 'Solidity.Backend.MemoryOps.referenceSlice_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms referenceSlice_empty
end Solidity.Backend.MemoryOps
