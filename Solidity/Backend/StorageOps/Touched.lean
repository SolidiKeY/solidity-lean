import Solidity.Storage.HashedLayout
import Solidity.Backend.StorageOps.Commutation
import Solidity.Backend.StorageOps.Traversal

/-!
Finite operation-generated slot terms and their word images under the existing
per-run region premise. This is address transport, not a new storage
representation. A compiler/layout adapter must still prove the supplied bounds
and run-preimage inclusions for its actual emitted accesses.
-/

namespace Solidity.Backend.StorageOps

open Solidity.Storage Solidity.Hash TypeGraph

/-- Candidate element addresses for a traversal, in order.
`stride` comes from the published layout; nested leaf offsets are supplied by
that layout's caller. The header is separate from these element accesses. -/
def touched (base : Solidity.Storage.Loc) (stride count : Nat) : List Solidity.Storage.Loc :=
  (List.range count).map (fun i => base.add (i * stride))

theorem mem_touched (base q : Solidity.Storage.Loc) (stride count : Nat) :
    q ∈ touched base stride count ↔
      ∃ i, i < count ∧ base.add (i * stride) = q := by
  simp only [touched, List.mem_map, List.mem_range]

theorem touched_length (base : Solidity.Storage.Loc) (stride count : Nat) :
    (touched base stride count).length = count := by
  simp only [touched, List.length_map, List.length_range]

/-- Positive layout stride identifies an element index at the symbolic level.
This uses constructor arithmetic, not any hash premise. -/
theorem touched_index_iff (base : Solidity.Storage.Loc) (stride count i : Nat)
    (positive : 0 < stride) :
    base.add (i * stride) ∈ touched base stride count ↔ i < count := by
  rw [mem_touched]
  constructor
  · rintro ⟨j, inside, equal⟩
    have products : j * stride = i * stride := by
      cases base <;> simp only [Solidity.Storage.Loc.add,
        Solidity.Storage.Loc.root.injEq, Solidity.Storage.Loc.hash.injEq,
        Solidity.Storage.Loc.data.injEq, true_and] at equal <;> omega
    have same : j = i := Nat.eq_of_mul_eq_mul_right positive products
    exact same ▸ inside
  · intro inside
    exact ⟨i, inside, rfl⟩

/-- The candidate touched list for the exact runtime count of `copyArray`.
A layout adapter still has to justify base/stride and enumerate nested leaves. -/
def copyTouched {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (base : Solidity.Storage.Loc) (stride : Nat) (old src : Value G (.array E)) :
    List Solidity.Storage.Loc := touched base stride (max old.length.val src.length.val)

/-- Connect the finite candidate access set to the actual runtime loop's frame.
The positive stride is a layout fact; it is not a new cryptographic premise. -/
theorem visit_frame_of_not_touched {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (target initial : Fin extent → Slot G E) (base : Solidity.Storage.Loc)
    (stride count : Nat) (i : Fin extent) (positive : 0 < stride)
    (outside : base.add (i.val * stride) ∉ touched base stride count) :
    visit target count initial i = initial i := by
  apply visit_frame target initial count i
  have notBefore : ¬ i.val < count := fun h =>
    outside ((touched_index_iff base stride count i.val positive).2 h)
  omega

/-- Exact finite-set transport: membership in the numeric image reflects
symbolic membership for bounded queries in this same run. No injectivity is
asserted outside the run, and the query's own preimages must be included. -/
theorem touched_word_iff {N L R : Nat} {H : Pre → Nat} {P : List Pre}
    (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (regions : RegionsDisjoint N L H (List.range R) P)
    (base q : Solidity.Storage.Loc) (stride count : Nat)
    (bounded : ∀ l ∈ touched base stride count, l.Bounded L R)
    (hashed : ∀ l ∈ touched base stride count, ∀ p ∈ l.pres N H, p ∈ P)
    (queryBounded : q.Bounded L R) (queryHashed : ∀ p ∈ q.pres N H, p ∈ P) :
    q.word N H ∈ (touched base stride count).map (Solidity.Storage.Loc.word N H) ↔
      q ∈ touched base stride count := by
  constructor
  · intro member
    obtain ⟨l, belongs, equal⟩ := List.mem_map.mp member
    have same : l = q := Solidity.Storage.Loc.word_inj hH hL hR regions l q
      (bounded l belongs) queryBounded (hashed l belongs) queryHashed equal
    exact same ▸ belongs
  · intro member
    exact List.mem_map.mpr ⟨q, member, rfl⟩

/-- The traversal-generated finite set preserves distinctness under word
transport. Duplicate accesses, if present, are not silently removed. -/
theorem touched_word_nodup {N L R : Nat} {H : Pre → Nat} {P : List Pre}
    (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (regions : RegionsDisjoint N L H (List.range R) P)
    (base : Solidity.Storage.Loc) (stride count : Nat)
    (bounded : ∀ l ∈ touched base stride count, l.Bounded L R)
    (hashed : ∀ l ∈ touched base stride count, ∀ p ∈ l.pres N H, p ∈ P)
    (distinct : (touched base stride count).Nodup) :
    ((touched base stride count).map (Solidity.Storage.Loc.word N H)).Nodup :=
  Solidity.Storage.Loc.nodup_map_word hH hL hR regions bounded hashed distinct

/-- Disjoint operation-generated symbolic access sets stay disjoint as words,
including when bases contain recursive mapping/array slot terms. -/
theorem touched_disjoint_words {N L R : Nat} {H : Pre → Nat} {P : List Pre}
    (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (regions : RegionsDisjoint N L H (List.range R) P)
    (a b : Solidity.Storage.Loc) (sa ca sb cb : Nat)
    (boundedA : ∀ l ∈ touched a sa ca, l.Bounded L R)
    (boundedB : ∀ l ∈ touched b sb cb, l.Bounded L R)
    (hashedA : ∀ l ∈ touched a sa ca, ∀ p ∈ l.pres N H, p ∈ P)
    (hashedB : ∀ l ∈ touched b sb cb, ∀ p ∈ l.pres N H, p ∈ P)
    (separate : ∀ l ∈ touched a sa ca, ∀ q ∈ touched b sb cb, l ≠ q) :
    ∀ l ∈ touched a sa ca, ∀ q ∈ touched b sb cb, l.word N H ≠ q.word N H := by
  intro l hl q hq equal
  exact separate l hl q hq (Solidity.Storage.Loc.word_inj hH hL hR regions l q
    (boundedA l hl) (boundedB q hq) (hashedA l hl) (hashedB q hq) equal)

/-- A pair of operation writes commutes after address transport, using only
this run's region premise and each generated address's bounds and preimages. -/
theorem generated_writes_commute {n N L R : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} {H : Pre → Nat} {P : List Pre}
    (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (regions : RegionsDisjoint N L H (List.range R) P)
    (a b : Solidity.Storage.Loc) (sa ca sb cb : Nat)
    (boundedA : ∀ l ∈ touched a sa ca, l.Bounded L R)
    (boundedB : ∀ l ∈ touched b sb cb, l.Bounded L R)
    (hashedA : ∀ l ∈ touched a sa ca, ∀ p ∈ l.pres N H, p ∈ P)
    (hashedB : ∀ l ∈ touched b sb cb, ∀ p ∈ l.pres N H, p ∈ P)
    (separate : ∀ l ∈ touched a sa ca, ∀ q ∈ touched b sb cb, l ≠ q)
    (l q : Solidity.Storage.Loc) (hl : l ∈ touched a sa ca) (hq : q ∈ touched b sb cb)
    (slots : Nat → Slot G E) (x y : Value G E) :
    Slots.write (Slots.write slots (l.word N H) x) (q.word N H) y =
      Slots.write (Slots.write slots (q.word N H) y) (l.word N H) x :=
  writes_commute slots _ _
    (touched_disjoint_words hH hL hR regions a b sa ca sb cb
      boundedA boundedB hashedA hashedB separate l hl q hq) x y

end Solidity.Backend.StorageOps
