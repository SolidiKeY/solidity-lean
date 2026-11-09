import Solidity.Backend.StorageOps.LayoutAccess
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Finite mapping/fixed-array access witnesses. No Source liveness, packing,
actual emitted-access correspondence or physical hash adequacy is inferred. -/
namespace H62.StorageAudit.LayoutWitnesses
open Solidity Solidity.Backend.StorageOps
open Solidity.Storage Solidity.Hash LayoutAccess

def ty : STy := .map (.sarr .word 2)
def base : Solidity.Storage.Loc := .root 0
def pathA : List Solidity.Storage.Step := [.key 7, .index 0]
def pathB : List Solidity.Storage.Step := [.key 7, .index 1]
def a : Solidity.Storage.Loc := .hash 7 base 0
def b : Solidity.Storage.Loc := .hash 7 base 1
def requestsA := [(pathA, 0), (pathA, 0)]
def requestsB := [(pathB, 0)]
def addressesA := [a, a]
def addressesB := [b]
def hash (_ : Pre) : Nat := 8
abbrev graph := CopyDemandControls.graph
def slots (index : Nat) : TypeGraph.Slot graph (.prim .bool) :=
  if index = b.word 32 hash then .present (.prim false) else .present (.prim true)
def clearEffect (_ : Nat) (v : TypeGraph.Value graph (.prim .bool)) :
    Option (TypeGraph.Value graph (.prim .bool)) := some v.clear
def setEffect (_ : Nat) (_ : TypeGraph.Value graph (.prim .bool)) :
    Option (TypeGraph.Value graph (.prim .bool)) := some (.prim true)
def result := TypeGraph.Slots.write
  (TypeGraph.Slots.write slots (a.word 32 hash) (.prim false)) (a.word 32 hash) (.prim false)

theorem fits : ty.Fits 4 := by
  change 2 ≤ 4 ∧ True
  decide

theorem placed : Placed 4 1 ty base :=
  placed_root (by decide)

theorem left_accepted : resolveMany ty base requestsA = some addressesA := by
  rfl

theorem right_accepted : resolveMany ty base requestsB = some addressesB := by
  rfl

theorem regions : RegionsDisjoint 32 4 hash (List.range 1)
    (runPreimages 32 hash (addressesA ++ addressesB)) := by
  decide

theorem hash_bound (pre : Pre) : hash pre < 32 := by
  change 8 < 32
  decide

theorem single_joint : ty.Fits 4 ∧ Placed 4 1 ty base ∧ resolve ty base pathA 0 = some a := by
  exact ⟨fits, placed, rfl⟩

theorem many_joint : ty.Fits 4 ∧ Placed 4 1 ty base ∧
    resolveMany ty base requestsA = some addressesA := by
  exact ⟨fits, placed, left_accepted⟩

theorem preimage_joint : a ∈ addressesA ∧ Pre.entry 7 0 ∈ a.pres 32 hash := by
  decide

theorem families_joint : (∀ pre, hash pre < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    ty.Fits 4 ∧ Placed 4 1 ty base ∧
    resolveMany ty base requestsA = some addressesA ∧
    resolveMany ty base requestsB = some addressesB ∧
    RegionsDisjoint 32 4 hash (List.range 1) (runPreimages 32 hash (addressesA ++ addressesB)) ∧
    (∀ x ∈ addressesA, ∀ y ∈ addressesB, x ≠ y) := by
  exact ⟨hash_bound, by decide, by decide, fits, placed, left_accepted,
    right_accepted, regions, by decide⟩

theorem performed : modifyMany clearEffect (addressesA.map (Solidity.Storage.Loc.word 32 hash)) slots =
    some result := by
  rfl

theorem outside_joint : (∀ pre, hash pre < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    ty.Fits 4 ∧ Placed 4 1 ty base ∧ resolveMany ty base requestsA = some addressesA ∧
    resolve ty base pathB 0 = some b ∧
    RegionsDisjoint 32 4 hash (List.range 1) (runPreimages 32 hash (addressesA ++ [b])) ∧
    b ∉ addressesA ∧
    modifyMany clearEffect (addressesA.map (Solidity.Storage.Loc.word 32 hash)) slots = some result := by
  exact ⟨hash_bound, by decide, by decide, fits, placed, left_accepted, rfl,
    regions, by decide, performed⟩

theorem families_apply :
    (modifyMany clearEffect (addressesA.map (Solidity.Storage.Loc.word 32 hash)) slots).bind
      (modifyMany setEffect (addressesB.map (Solidity.Storage.Loc.word 32 hash))) =
    (modifyMany setEffect (addressesB.map (Solidity.Storage.Loc.word 32 hash)) slots).bind
      (modifyMany clearEffect (addressesA.map (Solidity.Storage.Loc.word 32 hash))) := by
  first | rfl | decide | omega |
    exact resolved_families_commute hash_bound (by decide) (by decide) fits placed
      requestsA requestsB addressesA addressesB left_accepted right_accepted regions
      (by decide) slots clearEffect setEffect

theorem changed_and_preserved :
    ((modifyMany clearEffect (addressesA.map (Solidity.Storage.Loc.word 32 hash)) slots).bind
      (modifyMany setEffect (addressesB.map (Solidity.Storage.Loc.word 32 hash)))).map
      (fun next => (next (a.word 32 hash), next (b.word 32 hash))) =
        some (.present (.prim false), .present (.prim true)) := by
  rfl

theorem both_cells_change :
    ((slots (a.word 32 hash), slots (b.word 32 hash)),
     ((modifyMany clearEffect (addressesA.map (Solidity.Storage.Loc.word 32 hash)) slots).bind
       (modifyMany setEffect (addressesB.map (Solidity.Storage.Loc.word 32 hash)))).map
       (fun next => (next (a.word 32 hash), next (b.word 32 hash)))) =
      ((.present (.prim true), .present (.prim false)),
       some (.present (.prim false), .present (.prim true))) := by
  rfl

/-- This constant hash is admissible on the stated run only, not globally injective. -/
theorem extra_preimage_breaks_regions :
    ¬ RegionsDisjoint 32 4 hash (List.range 1) [.entry 7 0, .entry 8 0] := by
  decide

/-- Invalid later offsets reject the whole batch rather than dropping a request. -/
theorem later_bad_offset : resolveMany ty base [(pathA, 0), (pathB, 1)] = none := by
  rfl

theorem outside_apply : result (b.word 32 hash) = slots (b.word 32 hash) :=
  resolved_family_outside hash_bound (by decide) (by decide) fits placed
    requestsA addressesA left_accepted pathB 0 b rfl regions (by decide)
    slots result clearEffect performed

/-- info: 'H62.StorageAudit.LayoutWitnesses.fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fits
/-- info: 'H62.StorageAudit.LayoutWitnesses.placed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms placed
/-- info: 'H62.StorageAudit.LayoutWitnesses.left_accepted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms left_accepted
/-- info: 'H62.StorageAudit.LayoutWitnesses.right_accepted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms right_accepted
/-- info: 'H62.StorageAudit.LayoutWitnesses.regions' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms regions
/-- info: 'H62.StorageAudit.LayoutWitnesses.hash_bound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms hash_bound
/-- info: 'H62.StorageAudit.LayoutWitnesses.single_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms single_joint
/-- info: 'H62.StorageAudit.LayoutWitnesses.many_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms many_joint
/-- info: 'H62.StorageAudit.LayoutWitnesses.preimage_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms preimage_joint
/-- info: 'H62.StorageAudit.LayoutWitnesses.families_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms families_joint
/-- info: 'H62.StorageAudit.LayoutWitnesses.performed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms performed
/-- info: 'H62.StorageAudit.LayoutWitnesses.outside_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_joint
/-- info: 'H62.StorageAudit.LayoutWitnesses.families_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms families_apply
/-- info: 'H62.StorageAudit.LayoutWitnesses.changed_and_preserved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms changed_and_preserved
/-- info: 'H62.StorageAudit.LayoutWitnesses.extra_preimage_breaks_regions' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms extra_preimage_breaks_regions
/-- info: 'H62.StorageAudit.LayoutWitnesses.later_bad_offset' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms later_bad_offset
/-- info: 'H62.StorageAudit.LayoutWitnesses.outside_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_apply
/-- info: 'H62.StorageAudit.LayoutWitnesses.both_cells_change' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms both_cells_change
end H62.StorageAudit.LayoutWitnesses
