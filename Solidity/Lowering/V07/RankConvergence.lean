import Solidity.Lowering.V07.GraphRanks
namespace Solidity.Lowering.V07.RankConvergence
open RecursiveGraph
/-- Inline observations use only nodes below the given valid-rank threshold.
Dynamic arrays and mappings are guards; fixed arrays retain their weight. -/
theorem inline_below {n : Nat} (T : TypeGraph.Ty n) (r a b : Fin n → Nat) (k : Nat)
    (h : ∀ i, r i < k → a i = b i) (bound : T.inlineRank r < k) :
    T.inlineRank a = T.inlineRank b := by
  induction T with
  | prim p => rfl
  | node i => exact h i bound
  | array t ih => rfl
  | mapping key t ih => rfl
  | fixed t size ih =>
    have inner : t.inlineRank r < k := by
      change t.inlineRank r + 1 < k at bound
      omega
    exact congrArg (fun x => x + 1) (ih inner)

theorem fields_below {n : Nat} (fs : List (Name × TypeGraph.Ty n))
    (r a b : Fin n → Nat) (k : Nat)
    (h : ∀ i, r i < k → a i = b i)
    (bound : ∀ f ∈ fs, f.2.inlineRank r < k) :
    fs.foldr (fun f acc => max (f.2.inlineRank a) acc) 0 =
      fs.foldr (fun f acc => max (f.2.inlineRank b) acc) 0 := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have field := inline_below f.2 r a b k h (bound f List.mem_cons_self)
    have tail := ih (fun g hg => bound g (List.mem_cons_of_mem f hg))
    change max (f.2.inlineRank a) _ = max (f.2.inlineRank b) _
    rw [field,tail]

/-- Each component stabilizes once the prefix reaches any positive valid
rank assignment. This proves convergence, not the producer's node-count bound.
The comparison rank is never supplied to the executable producer. -/
theorem iter_stable {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (r : Fin n → Nat) (positive : ∀ i, 0 < r i)
    (valid : ∀ i f, f ∈ fs i → f.2.inlineRank r < r i) :
    ∀ k i, r i ≤ k → rankIter fs k i = rankIter fs (k+1) i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hp := positive i
    omega
  | succ k ih =>
    intro i hi
    have agree : ∀ j, r j < r i → rankIter fs k j = rankIter fs (k+1) j := by
      intro j hj
      exact ih j (by omega)
    exact congrArg (fun x => x+1)
      (fields_below (fs i) r (rankIter fs k) (rankIter fs (k+1)) (r i) agree (valid i))

/-- A stabilized prefix has the actual strict field inequalities checked by
producer schemas; this is not a supplied preservation or admission premise. -/
theorem stable_guarded {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (k : Nat) (stable : ∀ i, rankIter fs k i = rankIter fs (k+1) i)
    (i : Fin n) (f : Name × TypeGraph.Ty n) (member : f ∈ fs i) :
    f.2.inlineRank (rankIter fs k) < rankIter fs k i := by
  have le : f.2.inlineRank (rankIter fs k) ≤
      (fs i).foldr (fun g acc => max (g.2.inlineRank (rankIter fs k)) acc) 0 := by
    generalize fs i = fields at member ⊢
    induction fields with
    | nil => cases member
    | cons g gs ih =>
      have cases := List.mem_cons.mp member
      cases cases with
      | inl eq => subst f; exact Nat.le_max_left _ _
      | inr hm => exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)
  have same := stable i
  change rankIter fs k i = _ + 1 at same
  omega
end Solidity.Lowering.V07.RankConvergence
