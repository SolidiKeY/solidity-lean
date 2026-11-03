import Solidity.Lowering.V07.RecursiveGraph

/-! Monotone finite layout-rank propagation over existing graph metadata.
No source acceptance, path-depth bound or completeness premise is introduced. -/
namespace Solidity.Lowering.V07.GraphRanks
open RecursiveGraph

theorem inline_mono {n : Nat} (T : TypeGraph.Ty n) (r s : Fin n → Nat)
    (h : ∀ i, r i ≤ s i) : T.inlineRank r ≤ T.inlineRank s := by
  induction T with
  | prim p => exact Nat.le_refl 0
  | node i => exact h i
  | array t ih => exact Nat.le_refl 0
  | fixed t m ih => exact Nat.succ_le_succ ih
  | mapping k t ih => exact Nat.le_refl 0

theorem fold_mono {n : Nat} (fs : List (Name × TypeGraph.Ty n)) (r s : Fin n → Nat)
    (h : ∀ i, r i ≤ s i) :
    fs.foldr (fun f acc => max (f.2.inlineRank r) acc) 0 ≤
      fs.foldr (fun f acc => max (f.2.inlineRank s) acc) 0 := by
  induction fs with
  | nil => exact Nat.le_refl 0
  | cons f fs ih =>
    have field := inline_mono f.2 r s h
    change max (f.2.inlineRank r) (fs.foldr (fun f acc => max (f.2.inlineRank r) acc) 0) ≤
      max (f.2.inlineRank s) (fs.foldr (fun f acc => max (f.2.inlineRank s) acc) 0)
    omega

theorem step_mono {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (r s : Fin n → Nat) (h : ∀ i, r i ≤ s i) (i : Fin n) :
    rankStep fs r i ≤ rankStep fs s i := Nat.succ_le_succ (fold_mono (fs i) r s h)

theorem iter_increasing {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (k : Nat) (i : Fin n) : rankIter fs k i ≤ rankIter fs (k+1) i := by
  induction k generalizing i with
  | zero => exact Nat.zero_le _
  | succ k ih => exact step_mono fs _ _ ih i

theorem fold_bound {n : Nat} (fs : List (Name × TypeGraph.Ty n)) (r : Fin n → Nat)
    (k : Nat) (positive : 0 < k) (h : ∀ f ∈ fs, f.2.inlineRank r < k) :
    fs.foldr (fun f acc => max (f.2.inlineRank r) acc) 0 < k := by
  induction fs with
  | nil => exact positive
  | cons f fs ih =>
    apply Nat.max_lt.mpr
    exact ⟨h f (List.mem_cons_self),ih (fun g hg => h g (List.mem_cons_of_mem f hg))⟩

/-- Every computed prefix is below every positive valid rank assignment.
The valid assignment is used for this bound only, NEVER passed to produce. -/
theorem iter_bound {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (r : Fin n → Nat) (positive : ∀ i, 0 < r i)
    (valid : ∀ i f, f ∈ fs i → f.2.inlineRank r < r i) (k : Nat) (i : Fin n) :
    rankIter fs k i ≤ r i := by
  induction k generalizing i with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have step := step_mono fs (rankIter fs k) r ih i
    have bound := fold_bound (fs i) r (r i) (positive i) (valid i)
    exact Nat.le_trans step (Nat.succ_le_of_lt bound)

end Solidity.Lowering.V07.GraphRanks
