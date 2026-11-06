import Solidity.Backend.StorageOps.OperationPush
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Concrete joint push premises and live/retained contrasts. Existing intrinsic
values only; no Source allocation identity or target/world rollback bridge. -/
namespace H62.StorageAudit.PushWitnesses
open Solidity Solidity.Backend.StorageOps TypeGraph
abbrev graph := CopyDemandControls.graph
def zero : Index := ⟨0, by decide⟩
def one : Index := ⟨1, by decide⟩
def scalar : Value graph (.array (.prim .bool)) :=
  .array ⟨2, by decide⟩ zero (by decide) (fun _ => .present (.prim true))
def scalarAfter := (operationPush scalar).getD scalar
def fresh : Value graph (.array (.prim .bool)) :=
  .array ⟨0, by decide⟩ zero (by decide) (fun i => Fin.elim0 i)
def freshAfter := (operationPush fresh).getD fresh
def child : Value graph (.array (.prim .bool)) :=
  .array ⟨1, by decide⟩ one (by decide) (fun _ => .present (.prim true))
def aggregate : Value graph (.array (.array (.prim .bool))) :=
  .array ⟨2, by decide⟩ zero (by decide) (fun _ => .present child)
def aggregateAfter := (operationPush aggregate).getD aggregate

def last : Index := ⟨2 ^ 256 - 1, by decide⟩
def saturated : Value graph (.array (.prim .bool)) :=
  .array ⟨2 ^ 256 - 1, by decide⟩ last (Nat.le_refl _) (fun _ => .present (.prim true))

theorem data_input : Nonempty (Value graph (.array (.prim .bool))) := ⟨scalar⟩
theorem capacity_input : Nonempty (Value graph (.array (.prim .bool))) := ⟨saturated⟩

theorem header_joint : operationPush scalar = some scalarAfter := by rfl

theorem kept_joint : operationPush aggregate = some aggregateAfter ∧
    ((.array (.prim .bool) : TypeGraph.Ty 0).isPrimitive = false ∨ zero.val ≠ aggregate.length.val) ∧
    zero.val < aggregate.extent.val := by
  exact ⟨rfl, Or.inl rfl, by decide⟩

theorem fresh_joint : fresh.extent.val = fresh.length.val ∧
    operationPush fresh = some freshAfter := by exact ⟨rfl, rfl⟩

theorem reset_joint : (.prim .bool : TypeGraph.Ty 0).isPrimitive = true ∧
    operationPush scalar = some scalarAfter := by exact ⟨rfl, rfl⟩

theorem scalar_reset :
    Step.get Value.dflt (.index zero) scalar = some (.prim true) ∧
    Step.get Value.dflt (.index zero) scalarAfter = some (.prim false) ∧
    Step.get Value.dflt (.index one) scalarAfter = some (.prim true) := by
  exact ⟨rfl, rfl, rfl⟩

theorem aggregate_keeps_identity :
    Step.get Value.dflt (.index zero) aggregateAfter = some child ∧
    Step.getLive Value.dflt (.index zero) aggregate = none ∧
    Step.getLive Value.dflt (.index zero) aggregateAfter = some child ∧
    Step.get Value.dflt (.index one) aggregateAfter = some child ∧
    Step.getLive Value.dflt (.index one) aggregateAfter = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fresh_default : Step.get Value.dflt (.index zero) freshAfter = some (.prim false) := by rfl

theorem capacity_failure_and_success : operationPush saturated = none ∧
    saturated.length.val + 1 = 2 ^ 256 ∧ operationPush fresh = some freshAfter := by
  exact ⟨rfl, by decide, rfl⟩

theorem header_apply : scalarAfter.length.val = scalar.length.val + 1 ∧
    scalarAfter.extent.val = max scalar.extent.val (scalar.length.val + 1) :=
  operationPush_header scalar scalarAfter header_joint

theorem kept_apply : Step.get Value.dflt (.index zero) aggregateAfter =
    Step.get Value.dflt (.index zero) aggregate :=
  operationPush_keeps aggregate aggregateAfter kept_joint.1 zero kept_joint.2.1 kept_joint.2.2

theorem fresh_apply : Step.get Value.dflt (.index fresh.length) freshAfter =
    some (Value.dflt (.prim .bool)) :=
  operationPush_fresh fresh freshAfter fresh_joint.1 fresh_joint.2

theorem reset_apply : Step.get Value.dflt (.index scalar.length) scalarAfter =
    some (Value.dflt (.prim .bool)) :=
  operationPush_reset scalar scalarAfter reset_joint.1 reset_joint.2

/-- info: 'H62.StorageAudit.PushWitnesses.data_input' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms data_input
/-- info: 'H62.StorageAudit.PushWitnesses.capacity_input' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms capacity_input
/-- info: 'H62.StorageAudit.PushWitnesses.header_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_joint
/-- info: 'H62.StorageAudit.PushWitnesses.kept_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kept_joint
/-- info: 'H62.StorageAudit.PushWitnesses.fresh_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_joint
/-- info: 'H62.StorageAudit.PushWitnesses.reset_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reset_joint
/-- info: 'H62.StorageAudit.PushWitnesses.scalar_reset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_reset
/-- info: 'H62.StorageAudit.PushWitnesses.aggregate_keeps_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aggregate_keeps_identity
/-- info: 'H62.StorageAudit.PushWitnesses.fresh_default' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_default
/-- info: 'H62.StorageAudit.PushWitnesses.capacity_failure_and_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_failure_and_success
/-- info: 'H62.StorageAudit.PushWitnesses.header_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_apply
/-- info: 'H62.StorageAudit.PushWitnesses.kept_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kept_apply
/-- info: 'H62.StorageAudit.PushWitnesses.fresh_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_apply
/-- info: 'H62.StorageAudit.PushWitnesses.reset_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reset_apply

/-- Same concrete results, now using the original semantic push premises. -/
theorem semantic_kept_joint : (.array (.prim .bool) : TypeGraph.Ty 0).isPrimitive = false ∧
    zero.val < aggregate.extent.val ∧ aggregate.push = some aggregateAfter := by
  exact ⟨rfl, by decide, rfl⟩

theorem semantic_fresh_joint : fresh.extent.val = fresh.length.val ∧
    fresh.push = some freshAfter := by exact ⟨rfl, rfl⟩

def popped := child.pop.getD child

theorem pop_joint : zero.val + 1 = child.length.val ∧ child.pop = some popped := by
  exact ⟨rfl, rfl⟩

theorem semantic_kept_apply : Step.get Value.dflt (.index zero) aggregateAfter =
    Step.get Value.dflt (.index zero) aggregate :=
  push_reused_reference aggregate aggregateAfter zero semantic_kept_joint.1
    semantic_kept_joint.2.1 semantic_kept_joint.2.2

theorem semantic_fresh_apply : Step.get Value.dflt (.index fresh.length) freshAfter =
    some (Value.dflt (.prim .bool)) :=
  push_fresh_default fresh freshAfter semantic_fresh_joint.1 semantic_fresh_joint.2

theorem pop_apply : Step.getLive Value.dflt (.index zero) popped = none :=
  pop_invalidates_live child popped zero pop_joint.1 pop_joint.2

/-- Pop preserves allocated extent, clears its old live word, and invalidates liveness. -/
theorem pop_observations : popped.length.val = 0 ∧ popped.extent.val = 1 ∧
    Step.get Value.dflt (.index zero) popped = some (.prim false) ∧
    Step.getLive Value.dflt (.index zero) popped = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- One real pop succeeds; the next fails. This is not a world rollback theorem. -/
theorem pop_twice_fails : child.pop = some popped ∧ popped.pop = none ∧
    child.pop.bind Value.pop = none := by exact ⟨rfl, rfl, rfl⟩

/-- info: 'H62.StorageAudit.PushWitnesses.semantic_kept_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_kept_joint
/-- info: 'H62.StorageAudit.PushWitnesses.semantic_fresh_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_fresh_joint
/-- info: 'H62.StorageAudit.PushWitnesses.pop_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pop_joint
/-- info: 'H62.StorageAudit.PushWitnesses.semantic_kept_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_kept_apply
/-- info: 'H62.StorageAudit.PushWitnesses.semantic_fresh_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_fresh_apply
/-- info: 'H62.StorageAudit.PushWitnesses.pop_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pop_apply
/-- info: 'H62.StorageAudit.PushWitnesses.pop_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pop_observations
/-- info: 'H62.StorageAudit.PushWitnesses.pop_twice_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pop_twice_fails
end H62.StorageAudit.PushWitnesses
