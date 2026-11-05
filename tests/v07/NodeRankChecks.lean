import Solidity.Lowering.V07.NodeRank
import Solidity.Lowering.V07.LocationProducerControls
import Solidity.Lowering.V07.RankConvergence
namespace Solidity.Lowering.V07.NodeRankChecks
open RecursiveGraph NodeRank

def comparison : Fin 3 → Nat := fun i => if i.val = 0 then 30 else if i.val = 1 then 20 else 10
def fields := LocationGraphProducer.targetFields LocationProducerControls.chain .memory

example : ∀ i, rankIter fields 3 i = rankIter fields 4 i :=
  stable_at_nodes fields comparison (by decide)
example : LocationGraphProducer.FieldsOK LocationProducerControls.chain .memory :=
  location_fields_ok _ _ (by decide) (by decide) (by decide) comparison (by decide)

-- Three fixed-array layers around a guarded self-reference: actual rank4>n1.
def weighted : Source.Env := ⟨[⟨.struct,"Weighted",none,true,.struct "Weighted"
  (.structMember (.array (.array (.array (.array (.userType ⟨"Weighted",[]⟩) .none)
    (.some (.lit (.num (.dec 2 0 0))))) (.some (.lit (.num (.dec 2 0 0)))))
    (.some (.lit (.num (.dec 2 0 0))))) "next") .nil⟩]⟩
def weightedFields := targetFields weighted .storage
example : ∀ i, rankIter weightedFields 1 i = rankIter weightedFields 2 i :=
  stable_at_nodes weightedFields (fun _ => 100) (by decide)
example : rankIter weightedFields 1 ⟨0,by decide⟩ > 1 := by decide

-- Empty field metadata is permitted by convergence, but not by FieldsOK.
example : ∀ i : Fin 1, rankIter (fun _ => []) 1 i = rankIter (fun _ => []) 2 i :=
  stable_at_nodes (fun _ => []) (fun _ => 0) (by decide)
example : ∀ i : Fin 0, rankIter (fun _ => []) 0 i = rankIter (fun _ => []) 1 i :=
  stable_at_nodes (fun _ => []) (fun _ => 0) (by decide)
example : rankIter fields 2 ⟨0,by decide⟩ ≠ rankIter fields 3 ⟨0,by decide⟩ := by decide
example : ¬ (∀ i : Fin 3, ∀ f ∈ fields i, f.2.inlineRank (fun _ => 1) < 1) := by decide

example (r : Fin 1 → Nat) : ¬ (∀ i f,
    f ∈ targetFields GraphAdmissionBoundary.directEnv .storage i → f.2.inlineRank r < r i) := by
  intro valid
  have bad := valid ⟨0,by decide⟩ ("next",.node ⟨0,by decide⟩) (by decide)
  change r ⟨0,by decide⟩ < r ⟨0,by decide⟩ at bad
  omega

/-- info: [3, 2, 1, 3, 3, 4, 4, 1, 0, 2] -/
#guard_msgs in
#eval IO.println (reprStr [height comparison ⟨0,by decide⟩,
  height comparison ⟨1,by decide⟩,height comparison ⟨2,by decide⟩,
  rankIter fields 3 ⟨0,by decide⟩,rankIter fields 4 ⟨0,by decide⟩,
  rankIter weightedFields 1 ⟨0,by decide⟩,rankIter weightedFields 2 ⟨0,by decide⟩,
  rankIter (fun _ : Fin 1 => []) 1 ⟨0,by decide⟩,
  (LocationGraphProducer.choices LocationProducerControls.chain .memory).length - 3,
  rankIter fields 2 ⟨0,by decide⟩])
end Solidity.Lowering.V07.NodeRankChecks
