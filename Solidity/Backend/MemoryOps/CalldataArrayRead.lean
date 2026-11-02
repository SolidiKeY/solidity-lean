import Solidity.Backend.MemoryOps.SliceBounds
import Solidity.Source.State

/-! Structural observations of every published decoded calldata array type,
including static arrays and reference-valued elements. These are table/finite
contents laws, not Source expression execution or a generic payload emitter. -/
namespace Solidity.Backend.MemoryOps

/-- Exact initial representation of an existing typed decoded object. -/
def DecodedArrayAt {D : Source.Layout} {τ : Source.STy} {n : Option Nat}
    (c : Source.Calldata D) (off len : Nat)
    (hn : ∀ m, n = some m → m = len) (xs : Fin len → Source.Data D τ) : Prop :=
  c.objects off = some ⟨.array .calldata τ n, .array len hn xs⟩

/-- Structural finite read from the actual table, preserving the element type. -/
def DecodedArrayRead {D : Source.Layout} (c : Source.Calldata D) (off : Nat)
    (τ : Source.STy) (n : Option Nat) (i : Nat) (v : Source.Data D τ) : Prop :=
  ∃ (len : Nat) (xs : Fin len → Source.Data D τ) (hi : i < len)
    (hn : ∀ m, n = some m → m = len),
    c.objects off = some ⟨.array .calldata τ n, .array len hn xs⟩ ∧ xs ⟨i, hi⟩ = v

/-- No desired transport property is a premise: injectivity of the existing
array constructor identifies its actual finite contents. -/
theorem decodedArrayRead_iff {D : Source.Layout} {τ : Source.STy} {n : Option Nat}
    {c : Source.Calldata D} {off len i : Nat}
    {hn : ∀ m, n = some m → m = len} {xs : Fin len → Source.Data D τ}
    (hc : DecodedArrayAt c off len hn xs) (v : Source.Data D τ) :
    DecodedArrayRead c off τ n i v ↔ ∃ hi : i < len, xs ⟨i, hi⟩ = v := by
  constructor
  · intro hr
    obtain ⟨len', ys, hi, hn', ho, he⟩ := hr
    rw [hc] at ho
    have hs := Option.some.inj ho
    injection hs with ht hd
    injection hd with hl hτ hnopt hlen hxs
    cases hl
    cases hτ
    cases hnopt
    cases hlen
    cases hxs
    exact ⟨hi, he⟩
  · rintro ⟨hi, hv⟩
    exact ⟨len, xs, hi, hn, hc, hv⟩

/-- Generic endpoint failure is an impossible table observation, not a newly
defined Source revert semantics. -/
theorem decodedArrayRead_overrun {D : Source.Layout} {τ : Source.STy} {n : Option Nat}
    {c : Source.Calldata D} {off len i : Nat}
    {hn : ∀ m, n = some m → m = len} {xs : Fin len → Source.Data D τ}
    (hc : DecodedArrayAt c off len hn xs) (hi : len ≤ i) (v : Source.Data D τ) :
    ¬ DecodedArrayRead c off τ n i v := by
  intro hr
  obtain ⟨hb, _⟩ := (decodedArrayRead_iff hc v).mp hr
  omega

/-- Captured decoded contents retain their actual existing element type. -/
def decodedArraySlice {D : Source.Layout} {τ : Source.STy} {len : Nat}
    (xs : Fin len → Source.Data D τ) (start stop : Nat) : List (Source.Data D τ) :=
  ((List.ofFn xs).drop start).take (stop - start)

theorem decodedArraySlice_length {D : Source.Layout} {τ : Source.STy} {len start stop : Nat}
    (xs : Fin len → Source.Data D τ) (hb : SliceBounds len start stop) :
    (decodedArraySlice xs start stop).length = stop - start := by
  apply SliceBounds.length
  simpa only [List.length_ofFn] using hb

/-- Every interior captured value has the actual immutable decoded read. -/
theorem decodedArraySlice_read {D : Source.Layout} {τ : Source.STy} {n : Option Nat}
    {c : Source.Calldata D} {off len start stop i : Nat}
    {hn : ∀ m, n = some m → m = len} {xs : Fin len → Source.Data D τ}
    (hc : DecodedArrayAt c off len hn xs) (hb : SliceBounds len start stop)
    (hi : i < stop - start) :
    ∃ v, (decodedArraySlice xs start stop)[i]? = some v ∧
      DecodedArrayRead c off τ n (start + i) v := by
  refine ⟨xs ⟨start + i, hb.index hi⟩, ?_, (decodedArrayRead_iff hc _).mpr ⟨hb.index hi, rfl⟩⟩
  rw [decodedArraySlice, SliceBounds.read hi, List.getElem?_ofFn]
  simp only [dif_pos (hb.index hi)]

/-- Nested view coordinates compose for arbitrary typed decoded contents. -/
theorem decodedArraySlice_compose {D : Source.Layout} {τ : Source.STy}
    {len start stop lo hi : Nat} (xs : Fin len → Source.Data D τ)
    (hb : SliceBounds len start stop) (hk : SliceBounds (stop - start) lo hi) :
    ((decodedArraySlice xs start stop).drop lo).take (hi - lo) =
      decodedArraySlice xs (start + lo) (start + hi) := by
  have ho := hb.ordered
  have ko := hk.ordered
  have kb := hk.bounded
  simp only [decodedArraySlice, List.drop_take, List.take_take, List.drop_drop,
    Nat.min_eq_left (show hi - lo ≤ stop - start - lo by omega)]
  congr 1
  omega

/-- info: 'Solidity.Backend.MemoryOps.decodedArrayRead_iff' does not depend on any axioms -/
#guard_msgs in #print axioms decodedArrayRead_iff
/-- info: 'Solidity.Backend.MemoryOps.decodedArrayRead_overrun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedArrayRead_overrun
/-- info: 'Solidity.Backend.MemoryOps.decodedArraySlice_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedArraySlice_length
/-- info: 'Solidity.Backend.MemoryOps.decodedArraySlice_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedArraySlice_read
/-- info: 'Solidity.Backend.MemoryOps.decodedArraySlice_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedArraySlice_compose
end Solidity.Backend.MemoryOps
