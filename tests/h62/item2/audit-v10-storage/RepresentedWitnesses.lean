import Solidity.Backend.StorageOps.ProducerInterfaceControls

/-! Joint populated read/write/scalar-self-copy premise witnesses. Uses the
existing concrete local endpoint, never a universal producer or Source oracle. -/
namespace H62.StorageAudit.RepresentedWitnesses
open Solidity Solidity.Backend.StorageOps
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open ProducerInterfaceControls

theorem base_fits : TargetOperations.KeysFit base := by
  exact True.intro

abbrev selected : Query graph (.prim .bool) := .word path

theorem target_observations : ∀ q ∈ queries,
    after.store.cells (TargetOperations.toSlot (q.location base)
      (TargetOperations.query_keysFit q base base_fits)) =
        TargetOperations.encodeWord (symbolic (q.location base)) := by
  intro q member
  exact state_endpoint.observations _ (state_endpoint.covered q member)

theorem read_joint : TargetOperations.KeysFit base ∧
    Represented root queries base symbolic ∧
    (∀ q ∈ queries, after.store.cells (TargetOperations.toSlot (q.location base)
      (TargetOperations.query_keysFit q base base_fits)) =
        TargetOperations.encodeWord (symbolic (q.location base))) ∧
    selected ∈ queries ∧ selected.read root = some word := by
  exact ⟨base_fits, state_endpoint.represented, target_observations,
    List.mem_singleton_self _, rfl⟩

theorem read_execution :
    Evm.run (TargetOperations.readCode (.root 0)) after =
      .ok { after with stack := .val (TargetOperations.encodeWord word) :: after.stack } 0 :=
  TargetOperations.represented_read root queries base base_fits symbolic after
    read_joint.2.1 target_observations selected read_joint.2.2.2.1 word read_joint.2.2.2.2

theorem write_joint : (∀ l ∈ locations, TargetOperations.KeysFit l) ∧
    TargetOperations.KeysFit base ∧
    (∀ l (member : l ∈ locations), after.store.cells
      (TargetOperations.toSlot l (state_endpoint.fitting l member)) =
        TargetOperations.encodeWord (symbolic l)) := by
  exact ⟨state_endpoint.fitting, base_fits, state_endpoint.observations⟩

/-- Same inputs jointly satisfy every frozen scalar represented_copy hypothesis.
The query frame is explicitly empty; this is not a disjoint nonempty frame test. -/
theorem copy_joint : FiniteRun 8 1 1 hash [] locations ∧
    Transport 8 hash locations symbolic numeric ∧
    root.find path = some (.prim true) ∧ recursiveCopyAt root path path = some root ∧
    TargetOperations.KeysFit base ∧
    Represented root [selected] base symbolic ∧ PathSupported path ∧
    (∀ q ∈ ([] : List (Query graph (.prim .bool))), q.apart path) ∧
    (∀ q ∈ ([] : List (Query graph (.prim .bool))), q.location base ≠ pathLoc path base) ∧
    pathLoc path base ∈ locations ∧ pathLoc path base ∈ locations ∧
    (∀ q ∈ ([] : List (Query graph (.prim .bool))), q.location base ∈ locations) ∧
    (∀ l ∈ locations, TargetOperations.KeysFit l) ∧
    (∀ l (member : l ∈ locations), after.store.cells
      (TargetOperations.toSlot l (state_endpoint.fitting l member)) =
        TargetOperations.encodeWord (symbolic l)) := by
  refine ⟨state_endpoint.run, state_endpoint.transport, rfl, rfl, base_fits,
    state_endpoint.represented, True.intro, ?_, ?_, List.mem_singleton_self _,
    List.mem_singleton_self _, ?_, state_endpoint.fitting, state_endpoint.observations⟩
  all_goals intro q impossible; exact False.elim (List.not_mem_nil impossible)

theorem self_copy_execution : Evm.run (TargetOperations.copyCode (.root 0) (.root 0)) after =
    .ok after 0 :=
  TargetOperations.run_copy_self _ _

/-- The unwritten target state does not meet this populated read's initial agreement. -/
theorem unwritten_target_disagrees : before.store.cells (.root 0) ≠
    TargetOperations.encodeWord (symbolic base) := by
  decide

def zero_word : Semantics.Word := PrimTy.toWord (p := .bool) false
def reset_target : Evm.Machine :=
  { ProducerInterfaceControls.after with
    store := Evm.WordStore.write ProducerInterfaceControls.after.store (.root 0)
      (TargetOperations.encodeWord zero_word).val }

theorem reset_execution : Evm.run (TargetOperations.writeCode (.root 0) zero_word) after =
    .ok reset_target 0 :=
  TargetOperations.run_write _ _ _

theorem reset_observations : ∀ l (member : l ∈ locations), reset_target.store.cells
    (TargetOperations.toSlot l (state_endpoint.fitting l member)) =
      TargetOperations.encodeWord (Representation.write symbolic base zero_word l) :=
  TargetOperations.write_agreement locations state_endpoint.fitting base base_fits
    zero_word symbolic after state_endpoint.observations

theorem reset_changes_word : (after.store (.root 0), reset_target.store (.root 0)) = (1, 0) := by
  rfl

/-- info: 'H62.StorageAudit.RepresentedWitnesses.base_fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms base_fits
/-- info: 'H62.StorageAudit.RepresentedWitnesses.target_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms target_observations
/-- info: 'H62.StorageAudit.RepresentedWitnesses.read_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_joint
/-- info: 'H62.StorageAudit.RepresentedWitnesses.read_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_execution
/-- info: 'H62.StorageAudit.RepresentedWitnesses.write_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_joint
/-- info: 'H62.StorageAudit.RepresentedWitnesses.copy_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_joint
/-- info: 'H62.StorageAudit.RepresentedWitnesses.self_copy_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms self_copy_execution
/-- info: 'H62.StorageAudit.RepresentedWitnesses.unwritten_target_disagrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unwritten_target_disagrees
/-- info: 'H62.StorageAudit.RepresentedWitnesses.reset_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reset_execution
/-- info: 'H62.StorageAudit.RepresentedWitnesses.reset_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reset_observations
/-- info: 'H62.StorageAudit.RepresentedWitnesses.reset_changes_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reset_changes_word
end H62.StorageAudit.RepresentedWitnesses
