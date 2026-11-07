import Solidity.Backend.StorageOps.OperationFamilies
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Typed scheduler fixtures. The generic append law is proved on the existing
scheduler, independently of these expected observations. -/
namespace H62.GenericStorageOps.AppendFixtures
open Solidity Solidity.Backend.StorageOps TypeGraph
abbrev graph := CopyDemandControls.graph
def slots (_ : Nat) : Slot graph (.prim .bool) := .present (.prim true)
def effect (key : Nat) (value : Value graph (.prim .bool)) : Option (Value graph (.prim .bool)) :=
  if key = 1 then none else some value.clear

def examples : List (List Nat × Option (Slot graph (.prim .bool))) :=
  [([], some (.present (.prim true))),
   ([0], some (.present (.prim false))),
   ([0, 0], some (.present (.prim false))),
   ([0, 1], none), ([1, 0], none)]

theorem observations_match :
    examples.map (fun item => (modifyMany effect item.1 slots).map (fun next => next 0)) =
      examples.map Prod.snd := by rfl

theorem every_split (left right : List Nat) : modifyMany effect (left ++ right) slots =
    (modifyMany effect left slots).bind (modifyMany effect right) :=
  modifyMany_append effect left right slots

theorem late_failure : modifyMany effect [0] slots =
    some (Slots.write slots 0 (.prim false)) ∧ modifyMany effect [0, 1] slots = none := by
  exact ⟨rfl, rfl⟩

theorem first_failure : modifyMany effect [1, 0] slots = none := by rfl

/-- info: 'H62.GenericStorageOps.AppendFixtures.observations_match' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms observations_match
/-- info: 'H62.GenericStorageOps.AppendFixtures.every_split' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms every_split
/-- info: 'H62.GenericStorageOps.AppendFixtures.late_failure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms late_failure
/-- info: 'H62.GenericStorageOps.AppendFixtures.first_failure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms first_failure
end H62.GenericStorageOps.AppendFixtures
