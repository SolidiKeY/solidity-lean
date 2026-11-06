import Solidity.Backend.StorageOps.OperationFamilies
import Solidity.Backend.StorageOps.Touched

/-! Transport finite operation families through the published per-run regions.
No new store representation, global hash injectivity or cryptographic premise.
The layout/emitted-access adapter must still supply bounds and preimages. -/

namespace Solidity.Backend.StorageOps

open TypeGraph Solidity.Storage Solidity.Hash

/-- Finite generated families commute after address transport. Each effect
uses only the addressed value and its fixed captured parameters. -/
theorem generated_families_commute {n N L R : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} {H : Pre → Nat} {P : List Pre}
    (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (regions : RegionsDisjoint N L H (List.range R) P)
    (a b : Solidity.Storage.Loc) (sa ca sb cb : Nat)
    (boundedA : ∀ l ∈ touched a sa ca, l.Bounded L R)
    (boundedB : ∀ l ∈ touched b sb cb, l.Bounded L R)
    (hashedA : ∀ l ∈ touched a sa ca, ∀ p ∈ l.pres N H, p ∈ P)
    (hashedB : ∀ l ∈ touched b sb cb, ∀ p ∈ l.pres N H, p ∈ P)
    (separate : ∀ l ∈ touched a sa ca, ∀ q ∈ touched b sb cb, l ≠ q)
    (slots : Nat → Slot G E) (f g : Nat → Value G E → Option (Value G E)) :
    (modifyMany f ((touched a sa ca).map (Solidity.Storage.Loc.word N H)) slots).bind
        (modifyMany g ((touched b sb cb).map (Solidity.Storage.Loc.word N H))) =
      (modifyMany g ((touched b sb cb).map (Solidity.Storage.Loc.word N H)) slots).bind
        (modifyMany f ((touched a sa ca).map (Solidity.Storage.Loc.word N H))) := by
  apply modifyMany_commute
  intro x hx y hy
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
  exact touched_disjoint_words hH hL hR regions a b sa ca sb cb
    boundedA boundedB hashedA hashedB separate l hl q hq

/-- A bounded query outside the finite generated symbolic footprint is
unchanged by a successful numeric-address operation family. Its own recursive
preimages must also belong to this run. No claim is made for unbounded aliases. -/
theorem generated_family_outside {n N L R : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} {H : Pre → Nat} {P : List Pre}
    (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (regions : RegionsDisjoint N L H (List.range R) P)
    (base query : Solidity.Storage.Loc) (stride count : Nat)
    (bounded : ∀ l ∈ touched base stride count, l.Bounded L R)
    (hashed : ∀ l ∈ touched base stride count, ∀ p ∈ l.pres N H, p ∈ P)
    (queryBounded : query.Bounded L R)
    (queryHashed : ∀ p ∈ query.pres N H, p ∈ P)
    (outside : query ∉ touched base stride count)
    (slots result : Nat → Slot G E)
    (effect : Nat → Value G E → Option (Value G E))
    (performed : modifyMany effect
      ((touched base stride count).map (Solidity.Storage.Loc.word N H)) slots = some result) :
    result (query.word N H) = slots (query.word N H) := by
  apply modifyMany_outside effect _ slots result (query.word N H) _ performed
  intro member
  exact outside ((touched_word_iff hH hL hR regions base query stride count
    bounded hashed queryBounded queryHashed).1 member)

end Solidity.Backend.StorageOps
