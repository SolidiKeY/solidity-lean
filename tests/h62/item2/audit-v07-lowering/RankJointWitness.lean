import Solidity.Lowering.V07.NodeRank

/-!
Guarded regression: separate rank assumptions or an empty node domain must not
masquerade as a simultaneous convergence witness. This nonempty two-node graph
has a primitive leaf and a fixed-array dependency. Positive comparison ranks
and all field inequalities coexist; stabilization is derived from the original
rank theorems. Comparison magnitudes are not executable depth or gas bounds.
-/
namespace Solidity.H62.AuditV07.RankJointWitness
open Solidity.Lowering.V07 RecursiveGraph

def fields : Fin 2 → List (Name × TypeGraph.Ty 2) :=
  Fin.cases [("leaf", .prim .bool)] (fun _ => [("child", .fixed (.node 0) ⟨3,by decide⟩)])

def ranks (i : Fin 2) : Nat := if i = 0 then 10 else 100

theorem positive : ∀ i, 0 < ranks i := by
  intro i
  unfold ranks
  split <;> decide

theorem valid : ∀ i f, f ∈ fields i → f.2.inlineRank ranks < ranks i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro f member
    have eq : f = ("leaf", TypeGraph.Ty.prim .bool) := List.mem_singleton.mp member
    subst f
    exact Nat.zero_lt_succ 9
  · intro f member
    have eq : f = ("child", TypeGraph.Ty.fixed (.node 0) ⟨3,by decide⟩) := List.mem_singleton.mp member
    subst f
    change (11 : Nat) < (if Fin.succ j = (0 : Fin 2) then 10 else 100)
    rw [if_neg (Fin.succ_ne_zero j)]
    decide

/-- Both premises and the derived node-count result hold for the same graph. -/
theorem joint_rank_inputs :
    ∃ (fs : Fin 2 → List (Name × TypeGraph.Ty 2)) (r : Fin 2 → Nat),
      (∀ i, 0 < r i) ∧
      (∀ i f, f ∈ fs i → f.2.inlineRank r < r i) ∧
      (∀ i, (fs i).isEmpty = false) ∧
      (∀ i, rankIter fs 2 i = rankIter fs 3 i) := by
  refine ⟨fields, ranks, positive, valid, ?_, NodeRank.stable_at_nodes fields ranks valid⟩
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

/-- The original count theorem applies without a positivity premise. -/
theorem count_stability (k : Nat) (i : Fin 2) (bound : NodeRank.height ranks i ≤ k) :
    rankIter fields k i = rankIter fields (k+1) i :=
  NodeRank.stable_by_count fields ranks valid k i bound

/-- The independent convergence theorem retains its explicit positive ranks. -/
theorem comparison_stability (k : Nat) (i : Fin 2) (bound : ranks i ≤ k) :
    rankIter fields k i = rankIter fields (k+1) i :=
  RankConvergence.iter_stable fields ranks positive valid k i bound

/-- A fixed-array dependency makes the second iteration necessary at the parent. -/
theorem parent_not_stable_at_one : rankIter fields 1 1 ≠ rankIter fields 2 1 := by
  change (2 : Nat) ≠ 3
  decide

/-- Actual computed ranks are much smaller than the proof-only comparison ranks. -/
theorem computed_ranks : rankIter fields 2 0 = 1 ∧ rankIter fields 2 1 = 3 :=
  ⟨rfl, rfl⟩

#print axioms positive
#print axioms valid
#print axioms joint_rank_inputs
#print axioms count_stability
#print axioms comparison_stability
#print axioms parent_not_stable_at_one
#print axioms computed_ranks
end Solidity.H62.AuditV07.RankJointWitness
