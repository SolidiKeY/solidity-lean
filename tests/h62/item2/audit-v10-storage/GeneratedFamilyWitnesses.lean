import Solidity.Backend.StorageOps.OperationTransport
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Nonempty operation-generated transport witnesses. Finite regions only;
no physical execution, Source admission or global hash injectivity. -/
namespace H62.StorageAudit.GeneratedFamilyWitnesses
open Solidity Solidity.Backend.StorageOps Solidity.Storage Solidity.Hash

def base : Solidity.Storage.Loc := .root 0
def a : Solidity.Storage.Loc := .hash 7 base 0
def b : Solidity.Storage.Loc := .hash 7 base 1
def hash (_ : Pre) : Nat := 8
def preimages : List Pre := [.entry 7 0]
abbrev graph := CopyDemandControls.graph
def slots (i : Nat) : TypeGraph.Slot graph (.prim .bool) :=
  if i = b.word 32 hash then .present (.prim false) else .present (.prim true)
def clearEffect (_ : Nat) (v : TypeGraph.Value graph (.prim .bool)) := some v.clear
def setEffect (_ : Nat) (_ : TypeGraph.Value graph (.prim .bool)) := some (.prim true : TypeGraph.Value graph (.prim .bool))
def result := TypeGraph.Slots.write
  (TypeGraph.Slots.write slots (a.word 32 hash) (.prim false)) (a.word 32 hash) (.prim false)

theorem hash_bound (p : Pre) : hash p < 32 := by change 8 < 32; decide
theorem regions : RegionsDisjoint 32 4 hash (List.range 1) preimages := by decide

theorem bounded_a : a.Bounded 4 1 := by
  change 0 < 1 ∧ 0 < 4
  decide
theorem bounded_b : b.Bounded 4 1 := by
  change 0 < 1 ∧ 1 < 4
  decide

theorem bounded_left : ∀ l ∈ touched a 0 2, l.Bounded 4 1 := by
  intro l h
  change l ∈ [a, a] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact bounded_a

theorem bounded_right : ∀ l ∈ touched b 1 1, l.Bounded 4 1 := by
  intro l h
  change l ∈ [b] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  subst l
  exact bounded_b

theorem hashed_left : ∀ l ∈ touched a 0 2, ∀ p ∈ l.pres 32 hash, p ∈ preimages := by
  intro l h
  change l ∈ [a, a] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact fun _ hp => hp

theorem hashed_right : ∀ l ∈ touched b 1 1, ∀ p ∈ l.pres 32 hash, p ∈ preimages := by
  intro l h
  change l ∈ [b] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  subst l
  exact fun _ hp => hp

theorem separate : ∀ l ∈ touched a 0 2, ∀ q ∈ touched b 1 1, l ≠ q := by decide

theorem families_joint : (∀ p, hash p < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    RegionsDisjoint 32 4 hash (List.range 1) preimages ∧
    (∀ l ∈ touched a 0 2, l.Bounded 4 1) ∧
    (∀ l ∈ touched b 1 1, l.Bounded 4 1) ∧
    (∀ l ∈ touched a 0 2, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    (∀ l ∈ touched b 1 1, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    (∀ l ∈ touched a 0 2, ∀ q ∈ touched b 1 1, l ≠ q) := by
  exact ⟨hash_bound, by decide, by decide, regions, bounded_left, bounded_right,
    hashed_left, hashed_right, separate⟩

theorem performed : modifyMany clearEffect ((touched a 0 2).map (Solidity.Storage.Loc.word 32 hash)) slots = some result := by rfl

theorem outside_joint : (∀ p, hash p < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    RegionsDisjoint 32 4 hash (List.range 1) preimages ∧
    (∀ l ∈ touched a 0 2, l.Bounded 4 1) ∧
    (∀ l ∈ touched a 0 2, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    b.Bounded 4 1 ∧ (∀ p ∈ b.pres 32 hash, p ∈ preimages) ∧
    b ∉ touched a 0 2 ∧
    modifyMany clearEffect ((touched a 0 2).map (Solidity.Storage.Loc.word 32 hash)) slots = some result := by
  exact ⟨hash_bound, by decide, by decide, regions, bounded_left, hashed_left,
    bounded_b, fun _ hp => hp, by decide, performed⟩

theorem commute :
    (modifyMany clearEffect ((touched a 0 2).map (Solidity.Storage.Loc.word 32 hash)) slots).bind
      (modifyMany setEffect ((touched b 1 1).map (Solidity.Storage.Loc.word 32 hash))) =
    (modifyMany setEffect ((touched b 1 1).map (Solidity.Storage.Loc.word 32 hash)) slots).bind
      (modifyMany clearEffect ((touched a 0 2).map (Solidity.Storage.Loc.word 32 hash))) :=
  generated_families_commute hash_bound (by decide) (by decide) regions a b 0 2 1 1
    bounded_left bounded_right hashed_left hashed_right separate slots clearEffect setEffect

theorem outside : result (b.word 32 hash) = slots (b.word 32 hash) :=
  generated_family_outside hash_bound (by decide) (by decide) regions a b 0 2 bounded_left
    hashed_left bounded_b (fun _ hp => hp) (by decide) slots result clearEffect performed

theorem nonempty_and_repeated : touched a 0 2 = [a, a] ∧ touched b 1 1 = [b] := by decide

theorem both_cells_change :
    ((slots (a.word 32 hash), slots (b.word 32 hash)),
     ((modifyMany clearEffect ((touched a 0 2).map (Solidity.Storage.Loc.word 32 hash)) slots).bind
       (modifyMany setEffect ((touched b 1 1).map (Solidity.Storage.Loc.word 32 hash)))).map
       (fun next => (next (a.word 32 hash), next (b.word 32 hash)))) =
      ((.present (.prim true), .present (.prim false)),
       some (.present (.prim false), .present (.prim true))) := by rfl

theorem extra_preimage_breaks_regions :
    ¬ RegionsDisjoint 32 4 hash (List.range 1) [.entry 7 0, .entry 8 0] := by decide

/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.hash_bound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms hash_bound
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.regions' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms regions
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.bounded_a' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms bounded_a
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.bounded_b' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms bounded_b
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.bounded_left' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms bounded_left
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.bounded_right' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms bounded_right
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.hashed_left' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms hashed_left
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.hashed_right' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms hashed_right
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.separate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms separate
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.families_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms families_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.performed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms performed
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.outside_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms outside_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commute
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.nonempty_and_repeated' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_and_repeated
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.both_cells_change' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms both_cells_change
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.extra_preimage_breaks_regions' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms extra_preimage_breaks_regions
end H62.StorageAudit.GeneratedFamilyWitnesses
