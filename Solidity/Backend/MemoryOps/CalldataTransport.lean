import Solidity.Backend.MemoryOps.CalldataArrayRead
import Solidity.Backend.MemoryOps.HeapSnapshot

/-! Initial element correspondence transports actual immutable decoded reads to
an existing typed heap overwrite. Captured MVal inputs already exist: this is
not a converter or payload emitter. The relation is an initial representation
premise, not preservation; concrete applications must discharge it separately. -/
namespace Solidity.Backend.MemoryOps

/-- Generic decoded-array slice transport. Length and element correspondence
are initial representation facts; the resulting memory reads are derived. -/
theorem decodedArray_overwrite_read {D : Source.Layout} {τ : Source.STy} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat}
    {hn : ∀ m, n = some m → m = len} {xs : Fin len → Source.Data D τ}
    (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H) (dst : HRef H R) (a : ArrTy R E)
    (values : List (MVal H E)) (hl : values.length = len)
    (rel : Source.Data D τ → MVal H E → Prop)
    (hr : ∀ j : Fin len, rel (xs j) (values[j.val]'(hl ▸ j.isLt)))
    (offset start stop i : Nat) (hb : SliceBounds len start stop)
    (hd : offset + ((values.drop start).take (stop - start)).length ≤ hp.len dst a)
    (hi : i < stop - start) :
    let out := overwriteSlice hp dst a offset ((values.drop start).take (stop - start)) hd
    ∃ s v, DecodedArrayRead c off τ n (start + i) s ∧
      (MObj.elems a (out.get dst))[offset + i]? = some v ∧ rel s v := by
  dsimp only
  have hj : start + i < values.length := by rw [hl]; exact hb.index hi
  refine ⟨xs ⟨start + i, hb.index hi⟩, values[start + i],
    (decodedArrayRead_iff hc _).mpr ⟨hb.index hi, rfl⟩, ?_, hr ⟨start + i, hb.index hi⟩⟩
  rw [overwriteSlice_inside]
  · rw [SliceBounds.read hi]
    exact List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩
  · have hv : SliceBounds values.length start stop := by rw [hl]; exact hb
    rw [hv.length]
    exact hi

/-- Combine the actual decoded read/element representation with arbitrary
other-object framing, retaining reference-valued payloads without fresh copies. -/
theorem decodedArray_overwrite_transport {D : Source.Layout} {τ : Source.STy} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat}
    {hn : ∀ m, n = some m → m = len} {xs : Fin len → Source.Data D τ}
    (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H) (dst : HRef H R) (q : HRef H Q)
    (a : ArrTy R E) (values : List (MVal H E)) (hl : values.length = len)
    (rel : Source.Data D τ → MVal H E → Prop)
    (hr : ∀ j : Fin len, rel (xs j) (values[j.val]'(hl ▸ j.isLt)))
    (offset start stop i : Nat) (hb : SliceBounds len start stop)
    (hd : offset + ((values.drop start).take (stop - start)).length ≤ hp.len dst a)
    (hi : i < stop - start) (hne : dst.id ≠ q.id) :
    let out := overwriteSlice hp dst a offset ((values.drop start).take (stop - start)) hd
    ∃ s v, DecodedArrayRead c off τ n (start + i) s ∧
      (MObj.elems a (out.get dst))[offset + i]? = some v ∧ rel s v ∧ out.get q = hp.get q := by
  obtain ⟨s, v, hs, hm, hr⟩ := decodedArray_overwrite_read hc hp dst a values hl rel hr offset start stop i hb hd hi
  exact ⟨s, v, hs, hm, hr, overwriteSlice_frame hp dst q a offset _ hd hne⟩

/-- info: 'Solidity.Backend.MemoryOps.decodedArray_overwrite_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decodedArray_overwrite_read
/-- info: 'Solidity.Backend.MemoryOps.decodedArray_overwrite_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decodedArray_overwrite_transport
end Solidity.Backend.MemoryOps
