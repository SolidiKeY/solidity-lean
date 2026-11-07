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

/-- Exact membership transport retains query coverage in the SAME run. -/
theorem membership_joint : (∀ p, hash p < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    RegionsDisjoint 32 4 hash (List.range 1) preimages ∧
    (∀ l ∈ touched a 0 2, l.Bounded 4 1) ∧
    (∀ l ∈ touched a 0 2, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    a.Bounded 4 1 ∧ (∀ p ∈ a.pres 32 hash, p ∈ preimages) := by
  exact ⟨hash_bound, by decide, by decide, regions, bounded_left, hashed_left,
    bounded_a, fun _ hp => hp⟩

theorem membership_apply :
    a.word 32 hash ∈ (touched a 0 2).map (Solidity.Storage.Loc.word 32 hash) ↔
      a ∈ touched a 0 2 :=
  touched_word_iff hash_bound (by decide) (by decide) regions a a 0 2 bounded_left
    hashed_left bounded_a (fun _ hp => hp)

/-- Distinctness is an additional premise, witnessed on a nonempty singleton. -/
theorem nodup_joint : (∀ p, hash p < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    RegionsDisjoint 32 4 hash (List.range 1) preimages ∧
    (∀ l ∈ touched b 1 1, l.Bounded 4 1) ∧
    (∀ l ∈ touched b 1 1, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    (touched b 1 1).Nodup := by
  exact ⟨hash_bound, by decide, by decide, regions, bounded_right, hashed_right, by decide⟩

theorem nodup_apply : ((touched b 1 1).map (Solidity.Storage.Loc.word 32 hash)).Nodup :=
  touched_word_nodup hash_bound (by decide) (by decide) regions b 1 1 bounded_right hashed_right (by decide)

theorem disjoint_joint : (∀ p, hash p < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    RegionsDisjoint 32 4 hash (List.range 1) preimages ∧
    (∀ l ∈ touched a 0 2, l.Bounded 4 1) ∧
    (∀ l ∈ touched b 1 1, l.Bounded 4 1) ∧
    (∀ l ∈ touched a 0 2, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    (∀ l ∈ touched b 1 1, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    (∀ l ∈ touched a 0 2, ∀ q ∈ touched b 1 1, l ≠ q) := families_joint

theorem disjoint_apply : ∀ l ∈ touched a 0 2, ∀ q ∈ touched b 1 1,
    l.word 32 hash ≠ q.word 32 hash :=
  touched_disjoint_words hash_bound (by decide) (by decide) regions a b 0 2 1 1
    bounded_left bounded_right hashed_left hashed_right separate

theorem write_joint : (∀ p, hash p < 32) ∧ 4 ≤ 32 ∧ 1 ≤ 32 ∧
    RegionsDisjoint 32 4 hash (List.range 1) preimages ∧
    (∀ l ∈ touched a 0 2, l.Bounded 4 1) ∧
    (∀ l ∈ touched b 1 1, l.Bounded 4 1) ∧
    (∀ l ∈ touched a 0 2, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    (∀ l ∈ touched b 1 1, ∀ p ∈ l.pres 32 hash, p ∈ preimages) ∧
    (∀ l ∈ touched a 0 2, ∀ q ∈ touched b 1 1, l ≠ q) ∧
    a ∈ touched a 0 2 ∧ b ∈ touched b 1 1 := by
  exact ⟨hash_bound, by decide, by decide, regions, bounded_left, bounded_right,
    hashed_left, hashed_right, separate, by decide, by decide⟩

theorem write_apply :
    TypeGraph.Slots.write (TypeGraph.Slots.write slots (a.word 32 hash) (.prim false))
      (b.word 32 hash) (.prim true) =
    TypeGraph.Slots.write (TypeGraph.Slots.write slots (b.word 32 hash) (.prim true))
      (a.word 32 hash) (.prim false) :=
  generated_writes_commute hash_bound (by decide) (by decide) regions a b 0 2 1 1
    bounded_left bounded_right hashed_left hashed_right separate a b (by decide)
    (by decide) slots (.prim false) (.prim true)

/-- Duplicate accesses are not removed or silently granted Nodup. -/
theorem duplicate_retained :
    (touched a 0 2).map (Solidity.Storage.Loc.word 32 hash) = [8, 8] ∧
    ¬ (touched a 0 2).Nodup := by decide

theorem positive_index_joint : 0 < (1 : Nat) := by decide

theorem frame_joint : 0 < (1 : Nat) ∧ a.add (2 * 1) ∉ touched a 1 1 := by decide

def target (_ : Fin 3) : TypeGraph.Slot graph (.prim .bool) := .present (.prim false)
def initial (i : Fin 3) := slots i.val

theorem frame_apply : visit target 1 initial ⟨2, by decide⟩ = initial ⟨2, by decide⟩ :=
  visit_frame_of_not_touched target initial a 1 1 ⟨2, by decide⟩ (by decide) (by decide)

theorem frame_changes_inside : visit target 1 initial ⟨0, by decide⟩ = .present (.prim false) ∧
    initial ⟨0, by decide⟩ = .present (.prim true) ∧
    visit target 1 initial ⟨2, by decide⟩ = initial ⟨2, by decide⟩ := by exact ⟨rfl, rfl, rfl⟩

/-- These two contracts have data binders only; they are not logical bundles. -/
theorem membership_inputs : Nonempty (Solidity.Storage.Loc × Solidity.Storage.Loc × Nat × Nat) :=
  ⟨(a, b, 1, 2)⟩
theorem length_inputs : Nonempty (Solidity.Storage.Loc × Nat × Nat) := ⟨(a, 0, 2)⟩

/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.membership_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms membership_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.membership_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms membership_apply
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.nodup_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms nodup_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.nodup_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nodup_apply
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.disjoint_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms disjoint_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.disjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms disjoint_apply
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.write_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms write_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.write_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_apply
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.duplicate_retained' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_retained
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.positive_index_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms positive_index_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.frame_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms frame_joint
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.frame_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frame_apply
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.frame_changes_inside' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms frame_changes_inside
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.membership_inputs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms membership_inputs
/-- info: 'H62.StorageAudit.GeneratedFamilyWitnesses.length_inputs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms length_inputs
end H62.StorageAudit.GeneratedFamilyWitnesses
