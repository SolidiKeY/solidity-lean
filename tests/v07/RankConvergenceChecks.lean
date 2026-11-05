import Solidity.Lowering.V07.RankConvergence
import Solidity.Lowering.V07.RecursiveGraphControls
namespace Solidity.Lowering.V07.RankConvergenceChecks
open RecursiveGraph RankConvergence

def fs := targetFields RecursiveGraphControls.chain .memory
def comparison : Fin 3 → Nat := fun i => if i.val = 0 then 30 else if i.val = 1 then 20 else 10

example (k : Nat) (later : 30 ≤ k) (i : Fin 3) :
    rankIter fs k i = rankIter fs (k+1) i := by
  exact iter_stable fs comparison (by decide) (by decide) k i
    (Nat.le_trans (by revert i; decide) later)

example (k : Nat) (later : 30 ≤ k) (i : Fin 3)
    (f : Name × TypeGraph.Ty 3) (member : f ∈ fs i) :
    f.2.inlineRank (rankIter fs k) < rankIter fs k i := by
  apply stable_guarded fs k (fun j =>
    iter_stable fs comparison (by decide) (by decide) k j
      (Nat.le_trans (by revert j; decide) later)) i f member

-- No node-count limit on runtime/source execution: these are graph metadata.
example : rankIter fs 2 ⟨0,by decide⟩ ≠ rankIter fs 3 ⟨0,by decide⟩ := by decide
example : ¬ (∀ i : Fin 3, 0 < (fun _ : Fin 3 => 0) i) := by decide
example : ¬ (∀ i : Fin 3, ∀ f ∈ fs i,
    f.2.inlineRank (fun _ => 1) < (fun _ : Fin 3 => 1) i) := by decide

-- Guarded recursion is permitted; the inline cycle is still unstable at prefix3.
example : ∀ i, rankIter (targetFields RecursiveGraphControls.fixedGuard .storage) 1 i =
    rankIter (targetFields RecursiveGraphControls.fixedGuard .storage) 2 i := by decide
example : rankIter (targetFields GraphAdmissionBoundary.directEnv .storage) 3 ⟨0,by decide⟩ ≠
    rankIter (targetFields GraphAdmissionBoundary.directEnv .storage) 4 ⟨0,by decide⟩ := by decide

/-- info: [2, 3, 3, 3, 3, 2, 4] -/
#guard_msgs in
#eval IO.println (reprStr [rankIter fs 2 ⟨0,by decide⟩,
  rankIter fs 3 ⟨0,by decide⟩,rankIter fs 4 ⟨0,by decide⟩,
  rankIter fs 30 ⟨0,by decide⟩,rankIter fs 31 ⟨0,by decide⟩,
  rankIter (targetFields RecursiveGraphControls.fixedGuard .storage) 1 ⟨0,by decide⟩,
  rankIter (targetFields GraphAdmissionBoundary.directEnv .storage) 4 ⟨0,by decide⟩])
end Solidity.Lowering.V07.RankConvergenceChecks
