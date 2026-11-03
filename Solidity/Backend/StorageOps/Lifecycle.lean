import Solidity.Semantics.RecursiveStorage.Arrays

/-! Operation-side lifecycle and failure laws on the existing intrinsic graph
arrays. The graph API is standalone; source admission, ordinary-state migration
and target allocation/rollback remain explicit prerequisites. -/

namespace Solidity.Backend.StorageOps

open TypeGraph

/-- Capacity failure is exactly the published semantic check, without a new
length bound imposed by this lane. -/
theorem push_fails_iff {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (v : Value G (.array E)) : v.push = none ↔ 2 ^ 256 ≤ v.length.val + 1 := by
  cases v with
  | array extent length le slots =>
    simp only [Value.push, Value.length]
    split
    · constructor
      · intro impossible; cases impossible
      · intro impossible; omega
    · constructor
      · intro _; omega
      · intro _; rfl

/-- An empty pop fails, and every nonempty array admits a pop. -/
theorem pop_fails_iff {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (v : Value G (.array E)) : v.pop = none ↔ v.length.val = 0 := by
  cases v with
  | array extent length le slots =>
    simp only [Value.pop, Value.length]
    split
    · constructor
      · intro impossible; cases impossible
      · intro impossible; omega
    · constructor
      · intro _; omega
      · intro _; rfl

/-- A retained aggregate slot keeps its logical identity across push. This is
stronger than a live-only read and uses the selected existing slot semantics. -/
theorem push_reused_reference {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (v result : Value G (.array E)) (i : Index)
    (aggregate : E.isPrimitive = false) (retained : i.val < v.extent.val)
    (pushed : v.push = some result) :
    TypeGraph.Step.get Value.dflt (.index i) result =
      TypeGraph.Step.get Value.dflt (.index i) v :=
  v.push_keeps_slot Value.dflt result i (Or.inl aggregate) retained pushed

/-- A newly allocated slot reads as default, even for nested arrays. Reusing
an allocated aggregate slot is deliberately governed by the preceding law. -/
theorem push_fresh_default {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (v result : Value G (.array E))
    (fresh : v.extent.val = v.length.val) (pushed : v.push = some result) :
    TypeGraph.Step.get Value.dflt (.index v.length) result = some (Value.dflt E) := by
  cases v with
  | array extent length le slots =>
    simp only [Value.push] at pushed
    split at pushed
    next capacity =>
      cases pushed
      change extent.val = length.val at fresh
      have inside : length.val < max extent.val (length.val + 1) := by omega
      have outside : ¬ length.val < extent.val := by omega
      simp only [Value.length, TypeGraph.Step.get, dif_pos inside, dif_neg outside]
      split <;> rfl
    next capacity => cases pushed

/-- Pop invalidates the source-level live read of the removed element while
retaining the addressable extent. -/
theorem pop_invalidates_live {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (v result : Value G (.array E)) (i : Index)
    (last : i.val + 1 = v.length.val) (popped : v.pop = some result) :
    TypeGraph.Step.getLive Value.dflt (.index i) result = none := by
  have lengthEq := (v.pop_length result popped).1
  cases result with
  | array extent length le slots =>
    change length.val + 1 = v.length.val at lengthEq
    have outside : ¬ i.val < length.val := by omega
    simp only [TypeGraph.Step.getLive, if_neg outside]

end Solidity.Backend.StorageOps
