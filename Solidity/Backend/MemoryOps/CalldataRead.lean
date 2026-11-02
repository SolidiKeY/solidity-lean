import Solidity.Backend.MemoryOps.HeapSnapshot
import Solidity.Source.State

/-!
# Published decoded calldata objects and typed memory slice reads

The pinned source exposes `Calldata.objects` and `Data.array`, but no slice
execution judgment. These certificates observe those actual decoded objects.
They do not decode bytes, emit a payload, or define source expression semantics.
The input object equality is an initial representation premise, not a desired
preservation premise. General source lowering and ABI decoding remain open.
-/
namespace Solidity.Backend.MemoryOps

/-- The existing source array constructor instantiated with Boolean leaves. -/
def decodedBools {D : Source.Layout} (bs : List Bool) :
    Source.Data D (.array .calldata .bool none) :=
  .array bs.length (fun _ h => by cases h) (fun j => .val (.bool bs[j]))

/-- A certificate about an actual immutable decoded-object lookup. -/
def DecodedBoolArray {D : Source.Layout} (c : Source.Calldata D) (off : Nat)
    (bs : List Bool) : Prop :=
  c.objects off = some ⟨.array .calldata .bool none, decodedBools bs⟩

/-- A finite element observation of the published decoded array contents.
This is not the missing S02 source-expression read judgment. -/
def DecodedBoolRead {D : Source.Layout} (c : Source.Calldata D) (off i : Nat)
    (b : Bool) : Prop :=
  ∃ (n : Nat) (xs : Fin n → Source.Data D .bool) (hi : i < n)
    (hn : ∀ m, (none : Option Nat) = some m → m = n),
    c.objects off = some ⟨.array .calldata .bool none, .array n hn xs⟩ ∧
      xs ⟨i, hi⟩ = .val (.bool b)

theorem decodedBoolArray_read {D : Source.Layout} {c : Source.Calldata D}
    {off : Nat} {bs : List Bool} (hc : DecodedBoolArray c off bs)
    (i : Nat) (hi : i < bs.length) : DecodedBoolRead c off i bs[i] := by
  refine ⟨bs.length, (fun j => .val (.bool bs[j])), hi, (fun _ h => by cases h), ?_, rfl⟩
  exact hc

/-- No observation can supply an index outside the actual decoded object. -/
theorem decodedBoolRead_bound {D : Source.Layout} {c : Source.Calldata D}
    {off i : Nat} {bs : List Bool} {b : Bool} (hc : DecodedBoolArray c off bs)
    (hr : DecodedBoolRead c off i b) : i < bs.length := by
  obtain ⟨n, xs, hi, hn, ho, _⟩ := hr
  rw [hc] at ho
  have hsigma := Option.some.inj ho
  injection hsigma with htype hdata
  have hd : decodedBools bs = Source.Data.array n hn xs := hdata
  unfold decodedBools at hd
  injection hd with hl
  omega

/-- A structural decoded read has exactly the value of the original array. -/
theorem decodedBoolRead_iff {D : Source.Layout} {c : Source.Calldata D}
    {off i : Nat} {bs : List Bool} {b : Bool} (hc : DecodedBoolArray c off bs) :
    DecodedBoolRead c off i b ↔ bs[i]? = some b := by
  constructor
  · intro hr
    obtain ⟨n, xs, hi, hn, ho, helem⟩ := hr
    rw [hc] at ho
    have hsigma := Option.some.inj ho
    injection hsigma with htype hdata
    unfold decodedBools at hdata
    injection hdata with hloc hty hnopt hlen hxs
    cases hloc
    cases hty
    cases hnopt
    cases hlen
    cases hxs
    have hb : bs[i] = b := by
      injection helem with htyv hv
      injection hv with hb
    exact List.getElem?_eq_some_iff.mpr ⟨hi, hb⟩
  · intro hb
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hb
    simpa only [he] using decodedBoolArray_read hc i hi

/-- Exact endpoint certificates give real finite decoded-object reads. -/
theorem decodedBoolSlice_read {D : Source.Layout} {c : Source.Calldata D}
    {off : Nat} {bs : List Bool} (hc : DecodedBoolArray c off bs)
    {start stop i : Nat} (hb : SliceBounds bs.length start stop)
    (hi : i < stop - start) :
    DecodedBoolRead c off (start + i) (bs[start + i]'(hb.index hi)) :=
  decodedBoolArray_read hc (start + i) (hb.index hi)

/-- An endpoint overrun is an impossible decoded read, not an invented source
revert observation. The source halt classification still belongs to S02. -/
theorem decodedBoolRead_overrun {D : Source.Layout} {c : Source.Calldata D}
    {off : Nat} {bs : List Bool} (hc : DecodedBoolArray c off bs)
    {i : Nat} (hi : bs.length ≤ i) (b : Bool) : ¬ DecodedBoolRead c off i b := by
  intro hr
  have hl := decodedBoolRead_bound hc hr
  omega

/-- The existing heap overwrite receives the captured decoded Boolean slice.
Every interior result agrees with a finite read of the original calldata
object. No arbitrary payload cap or source preservation assumption occurs. -/
theorem decodedBoolSlice_overwrite_read {D : Source.Layout} {c : Source.Calldata D}
    {off : Nat} {bs : List Bool} (hc : DecodedBoolArray c off bs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (offset start stop i : Nat)
    (hb : SliceBounds bs.length start stop)
    (hd : offset + ((bs.drop start).take (stop - start)).length ≤ hp.len dst a)
    (hi : i < stop - start) :
    let out := overwriteSlice hp dst a offset ((bs.drop start).take (stop - start)) hd
    ∃ b, (MObj.elems a (out.get dst))[offset + i]? = some b ∧
      DecodedBoolRead c off (start + i) b := by
  dsimp only
  refine ⟨bs[start + i]'(hb.index hi), ?_, decodedBoolSlice_read hc hb hi⟩
  rw [overwriteSlice_inside]
  · rw [SliceBounds.read hi]
    exact List.getElem?_eq_some_iff.mpr ⟨hb.index hi, rfl⟩
  · rw [hb.length]
    exact hi

/-- Combine an actual decoded-source read, the destination observation and
framing of a different typed object. The input lookup premise is discharged
in the concrete controls; no source execution relation is assumed. -/
theorem decodedBoolSlice_transport {D : Source.Layout} {c : Source.Calldata D}
    {off : Nat} {bs : List Bool} (hc : DecodedBoolArray c off bs)
    {H : HTy} {R Q : RefTy} (hp : Heap H) (dst : HRef H R) (q : HRef H Q)
    (a : ArrTy R (.prim .bool)) (offset start stop i : Nat)
    (hb : SliceBounds bs.length start stop)
    (hd : offset + ((bs.drop start).take (stop - start)).length ≤ hp.len dst a)
    (hi : i < stop - start) (hne : dst.id ≠ q.id) :
    let out := overwriteSlice hp dst a offset ((bs.drop start).take (stop - start)) hd
    ∃ b, (MObj.elems a (out.get dst))[offset + i]? = some b ∧
      DecodedBoolRead c off (start + i) b ∧ out.get q = hp.get q := by
  obtain ⟨b, hm, hr⟩ := decodedBoolSlice_overwrite_read hc hp dst a offset start stop i hb hd hi
  exact ⟨b, hm, hr, overwriteSlice_frame hp dst q a offset _ hd hne⟩

/-- info: 'Solidity.Backend.MemoryOps.decodedBoolRead_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms decodedBoolRead_iff
/-- info: 'Solidity.Backend.MemoryOps.decodedBoolRead_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedBoolRead_bound
/-- info: 'Solidity.Backend.MemoryOps.decodedBoolSlice_overwrite_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedBoolSlice_overwrite_read
/-- info: 'Solidity.Backend.MemoryOps.decodedBoolSlice_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedBoolSlice_transport

end Solidity.Backend.MemoryOps
