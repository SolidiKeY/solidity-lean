import Solidity.Lowering.V07.RankConvergence
import Solidity.Lowering.V07.LocationGraphProducer
namespace Solidity.Lowering.V07.NodeRank
open RecursiveGraph
/-- Number of existing nodes with strictly smaller comparison rank, plus one.
A proof-side finite count, not a runtime/source depth or representation bound. -/
def height {n : Nat} (r : Fin n → Nat) (i : Fin n) : Nat :=
  ((List.finRange n).filter fun j => decide (r j < r i)).length + 1

theorem height_le {n : Nat} (r : Fin n → Nat) (i : Fin n) : height r i ≤ n := by
  have mem : i ∈ List.finRange n := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val,by simpa only [List.length_finRange] using i.isLt,?_⟩
    simp only [List.getElem_finRange]
    apply Fin.ext
    rfl
  have shorter := List.length_filter_lt_length_iff_exists.mpr
    (show ∃ j ∈ List.finRange n, ¬ decide (r j < r i) = true from
      ⟨i,mem,by simp only [Nat.lt_irrefl,decide_false,Bool.false_eq_true,not_false_eq_true]⟩)
  simp only [List.length_finRange] at shorter
  unfold height
  omega

theorem height_strict {n : Nat} (r : Fin n → Nat) (i j : Fin n) (h : r j < r i) :
    height r j < height r i := by
  have mem : j ∈ List.finRange n := by
    apply List.mem_iff_getElem.mpr
    refine ⟨j.val,by simpa only [List.length_finRange] using j.isLt,?_⟩
    simp only [List.getElem_finRange]
    apply Fin.ext
    rfl
  have nested : ((List.finRange n).filter fun k => decide (r k < r i)).filter
      (fun k => decide (r k < r j)) =
      (List.finRange n).filter (fun k => decide (r k < r j)) := by
    rw [List.filter_filter]
    apply congrArg (fun p => (List.finRange n).filter p)
    funext k
    by_cases hk : r k < r j
    · simp only [hk,Nat.lt_trans hk h,decide_true,Bool.true_and]
    · simp only [hk,decide_false,Bool.false_and]
  have shorter := List.length_filter_lt_length_iff_exists.mpr
    (show ∃ k ∈ ((List.finRange n).filter fun k => decide (r k < r i)),
        ¬ decide (r k < r j) = true from
      ⟨j,List.mem_filter.mpr ⟨mem,by simp only [h,decide_true]⟩,
        by simp only [Nat.lt_irrefl,decide_false,Bool.false_eq_true,not_false_eq_true]⟩)
  rw [nested] at shorter
  unfold height
  omega

/-- Finite comparison order, rather than the magnitudes of comparison ranks,
controls when each actual rankIter component stabilizes. -/
theorem stable_by_count {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (r : Fin n → Nat) (valid : ∀ i f, f ∈ fs i → f.2.inlineRank r < r i) :
    ∀ k i, height r i ≤ k → rankIter fs k i = rankIter fs (k+1) i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    unfold height at hi
    omega
  | succ k ih =>
    intro i hi
    have agree : ∀ j, r j < r i → rankIter fs k j = rankIter fs (k+1) j := by
      intro j hj
      have smaller := height_strict r i j hj
      exact ih j (by omega)
    exact congrArg (fun x => x+1)
      (RankConvergence.fields_below (fs i) r (rankIter fs k) (rankIter fs (k+1))
        (r i) agree (valid i))

/-- Actual node-count stabilization whenever ANY valid rank assignment exists.
The comparison rank is proof-only and never passed to an executable producer.
Source admission and existence of such a rank remain separate obligations. -/
theorem stable_at_nodes {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (r : Fin n → Nat) (valid : ∀ i f, f ∈ fs i → f.2.inlineRank r < r i) :
    ∀ i, rankIter fs n i = rankIter fs (n+1) i :=
  fun i => stable_by_count fs r valid n i (height_le r i)

/-- The producer's actual node-count ranks satisfy its guardedness check
if a valid comparison assignment exists; no desired-result premise is used. -/
theorem guarded_at_nodes {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (r : Fin n → Nat) (valid : ∀ i f, f ∈ fs i → f.2.inlineRank r < r i)
    (i : Fin n) (f : Name × TypeGraph.Ty n) (member : f ∈ fs i) :
    f.2.inlineRank (rankIter fs n) < rankIter fs n i :=
  RankConvergence.stable_guarded fs n (stable_at_nodes fs r valid) i f member
/-- Discharge the executable location producer's rank-check conjunct from
any valid comparison assignment. Field support, nonemptiness and name
uniqueness remain explicit; no Source admission or refusal is inferred. -/
theorem location_fields_ok (E : Source.Env) (loc : Source.DataLoc)
    (present : ∀ i, (LocationGraphProducer.fieldCertificate E loc i).isSome = true)
    (nonempty : ∀ i, (LocationGraphProducer.targetFields E loc i).isEmpty = false)
    (distinct : ∀ i, Semantics.nodupKeysB (LocationGraphProducer.targetFields E loc i) = true)
    (r : Fin (LocationGraphProducer.choices E loc).length → Nat)
    (valid : ∀ i f, f ∈ LocationGraphProducer.targetFields E loc i → f.2.inlineRank r < r i) :
    LocationGraphProducer.FieldsOK E loc := by
  intro i
  refine ⟨present i,nonempty i,distinct i,?_⟩
  apply List.all_eq_true.mpr
  intro f member
  exact decide_eq_true (guarded_at_nodes (LocationGraphProducer.targetFields E loc) r valid i f member)
end Solidity.Lowering.V07.NodeRank
