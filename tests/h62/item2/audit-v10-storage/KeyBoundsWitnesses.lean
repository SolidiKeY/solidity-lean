import Solidity.Backend.StorageOps.TargetOperations
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Joint witnesses for frozen slot-conversion key bounds. Key bounds do not
assert live graph reads, Source admission or physical hash separation. -/
namespace H62.StorageAudit.KeyBoundsWitnesses
open Solidity Solidity.Backend.StorageOps
open TypeGraph Solidity.Storage.Representation.Graph

abbrev graph := CopyDemandControls.graph
abbrev Root : TypeGraph.Ty 0 := .mapping .bool (.array (.prim .uint))
def base : Solidity.Storage.Loc := .hash 7 (.data (.root 3) 2) 5
def index : Index := ⟨3, by decide⟩
def step : TypeGraph.Step graph Root (.array (.prim .uint)) := .key true
def path : TypeGraph.Path graph Root (.prim .uint) :=
  .cons step (.cons (.index index) .nil)
def query : Query graph Root := .word path

theorem base_fits : TargetOperations.KeysFit base := by
  change 7 < Evm.W ∧ True
  decide

theorem conversion_joint : ∃ l : Solidity.Storage.Loc, TargetOperations.KeysFit l := by
  exact ⟨base, base_fits⟩

theorem injective_joint : ∃ a b : Solidity.Storage.Loc,
    ∃ fa : TargetOperations.KeysFit a, ∃ fb : TargetOperations.KeysFit b,
      TargetOperations.toSlot a fa = TargetOperations.toSlot b fb := by
  exact ⟨base, base, base_fits, base_fits, rfl⟩

theorem addition_joint : ∃ (l : Solidity.Storage.Loc) (_offset : Nat),
    TargetOperations.KeysFit l := by
  exact ⟨base, 9, base_fits⟩

theorem step_joint : ∃ (_s : TypeGraph.Step graph Root (.array (.prim .uint)))
    (l : Solidity.Storage.Loc), TargetOperations.KeysFit l := by
  exact ⟨step, base, base_fits⟩

theorem path_joint : ∃ (_p : TypeGraph.Path graph Root (.prim .uint))
    (l : Solidity.Storage.Loc), TargetOperations.KeysFit l := by
  exact ⟨path, base, base_fits⟩

theorem query_joint : ∃ (_q : Query graph Root) (l : Solidity.Storage.Loc),
    TargetOperations.KeysFit l := by
  exact ⟨query, base, base_fits⟩

/-- A natural key at W cannot be supplied to the bounded slot conversion. -/
theorem outside_word_bound : ¬ TargetOperations.KeysFit (.hash Evm.W (.root 3) 5) := by
  change ¬ (Evm.W < Evm.W ∧ True)
  decide

/-- A fitting symbolic address can still select an unavailable live graph read. -/
theorem fitting_is_not_liveness :
    TargetOperations.KeysFit base ∧ path.readLive Value.dflt (Value.dflt Root) = none := by
  exact ⟨base_fits, rfl⟩

/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.base_fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms base_fits
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.conversion_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms conversion_joint
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.injective_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms injective_joint
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.addition_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms addition_joint
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.step_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms step_joint
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.path_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms path_joint
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.query_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms query_joint
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.outside_word_bound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms outside_word_bound
/-- info: 'H62.StorageAudit.KeyBoundsWitnesses.fitting_is_not_liveness' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fitting_is_not_liveness
end H62.StorageAudit.KeyBoundsWitnesses
