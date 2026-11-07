import Solidity.Backend.StorageOps.LayoutAccess

/-! Nested layout resolution, complete finite preimages and actual operation
transport controls. Word-granularity layout only; no new source restriction. -/
namespace Solidity.Backend.StorageOps.LayoutControls
open Solidity.Storage Solidity.Hash LayoutAccess

private def layout : STy := .map (.map (.sarr (.strct [.word, .word]) 2))
private def root : Solidity.Storage.Loc := .root 0
private def pathA : List Solidity.Storage.Step := [.key 7, .key 9, .index 0, .field 1]
private def pathB : List Solidity.Storage.Step := [.key 7, .key 9, .index 1, .field 1]
private def base : Solidity.Storage.Loc := .hash 9 (.hash 7 root 0) 0
private def a : Solidity.Storage.Loc := base.add 1
private def b : Solidity.Storage.Loc := base.add 3

theorem nested_resolution : resolveMany layout root [(pathA, 0), (pathA, 0), (pathB, 0)] =
    some [a, a, b] := rfl

theorem repeated_length : [a, a, b].length = [(pathA, 0), (pathA, 0), (pathB, 0)].length :=
  resolveMany_length _ _ nested_resolution

/-- A later invalid request rejects the complete batch, not just that entry. -/
theorem late_invalid_path : resolveMany layout root [(pathA, 0), ([.field 0], 0)] = none := rfl

theorem invalid_offset : resolveMany layout root [(pathA, 0), (pathB, 1)] = none := rfl

/-- Boundary checks come from the published layout, not a new V10 profile cap. -/
theorem dynamic_last (i : Nat) (inside : i < lmax) :
    resolve (.darr .word) root [.index i] 0 = some (.data root i) := by
  simp only [resolve, STy.locate, inside, if_pos, STy.size, Nat.mul_one,
    Option.bind_eq_bind, Option.bind_some, Nat.zero_lt_one, Solidity.Storage.Loc.add_zero]

theorem dynamic_invalid : resolve (.darr .word) root [.index lmax] 0 = none := by
  simp only [resolve, STy.locate, Nat.lt_irrefl, if_false, Option.bind_eq_bind, Option.bind_none]

private def hash : Pre → Nat
  | .entry 7 0 => 32
  | .entry 9 32 => 64
  | _ => 128
private theorem hash_lt (p : Pre) : hash p < 256 := by
  cases p with
  | data w => change 128 < 256; decide
  | entry k w => simp only [hash]; split <;> decide

theorem complete_nested_preimages : runPreimages 256 hash [a, a, b] =
    [.entry 7 0, .entry 9 32, .entry 7 0, .entry 9 32, .entry 7 0, .entry 9 32] := rfl

private theorem regions : RegionsDisjoint 256 4 hash (List.range 1)
    (runPreimages 256 hash ([a, a] ++ [b])) := by decide
private theorem fits : layout.Fits 4 := by
  simp only [layout, STy.Fits, STy.FitsAll, STy.size, STy.sizes] <;> decide
private theorem placed : Placed 4 1 layout root := by
  intro j hj
  have zero : j = 0 := by change j < 1 at hj; omega
  subst j
  change 0 < 1
  decide

private def graph : TypeGraph.Schema 0 where
  origin := "v10-layout-operation-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def slots (_ : Nat) : TypeGraph.Slot graph (.prim .bool) := .present (.prim true)
private def clear (_ : Nat) (_ : TypeGraph.Value graph (.prim .bool)) : Option (TypeGraph.Value graph (.prim .bool)) := some (TypeGraph.Value.prim false)
private def set (_ : Nat) (_ : TypeGraph.Value graph (.prim .bool)) : Option (TypeGraph.Value graph (.prim .bool)) := some (TypeGraph.Value.prim true)

/-- Regression: repeated nested accesses admit their alias, while a distinct
checked sibling stays outside under the same complete per-run region policy. -/
theorem checked_alias_and_outside :
    a.word 256 hash ∈ [a, a].map (Solidity.Storage.Loc.word 256 hash) ∧
    b.word 256 hash ∉ [a, a].map (Solidity.Storage.Loc.word 256 hash) := by
  constructor
  · exact (resolved_word_membership hash_lt (by decide) (by decide) fits placed
      [(pathA, 0), (pathA, 0)] [a, a] rfl pathA 0 a rfl (by decide)).mpr List.mem_cons_self
  · intro member
    have symbolic := (resolved_word_membership hash_lt (by decide) (by decide) fits placed
      [(pathA, 0), (pathA, 0)] [a, a] rfl pathB 0 b rfl regions).mp member
    exact (by decide : b ∉ [a, a]) symbolic

/-- Regression: repeated nested requests retain two numeric occurrences;
a separate checked sibling has zero, rather than gaining an alias. -/
theorem checked_alias_multiplicity :
    ([a, a].map (Solidity.Storage.Loc.word 256 hash)).count (a.word 256 hash) = 2 ∧
    ([a, a].map (Solidity.Storage.Loc.word 256 hash)).count (b.word 256 hash) = 0 := by
  constructor
  · exact (resolved_word_count hash_lt (by decide) (by decide) fits placed
      [(pathA, 0), (pathA, 0)] [a, a] rfl pathA 0 a rfl (by decide)).trans (by decide)
  · exact (resolved_word_count hash_lt (by decide) (by decide) fits placed
      [(pathA, 0), (pathA, 0)] [a, a] rfl pathB 0 b rfl regions).trans (by decide)

/-- Nontrivial actual partial-operation families at checked nested addresses;
left repeats its access, and cross-family separation is checked. -/
theorem checked_operation_families :
    (modifyMany clear ([a, a].map (Solidity.Storage.Loc.word 256 hash)) slots).bind
      (modifyMany set ([b].map (Solidity.Storage.Loc.word 256 hash))) =
    (modifyMany set ([b].map (Solidity.Storage.Loc.word 256 hash)) slots).bind
      (modifyMany clear ([a, a].map (Solidity.Storage.Loc.word 256 hash))) :=
  resolved_families_commute hash_lt (by decide) (by decide) fits placed
    [(pathA, 0), (pathA, 0)] [(pathB, 0)] [a, a] [b] rfl rfl regions
    (by decide) slots clear set

theorem changed_first_preserved_second :
    ((modifyMany clear ([a, a].map (Solidity.Storage.Loc.word 256 hash)) slots).bind
      (modifyMany set ([b].map (Solidity.Storage.Loc.word 256 hash)))).map
        (fun result => (result (a.word 256 hash), result (b.word 256 hash))) =
      some (.present (.prim false), .present (.prim true)) := rfl

theorem checked_outside_query :
    (modifyMany clear ([a, a].map (Solidity.Storage.Loc.word 256 hash)) slots).map
      (fun result => result (b.word 256 hash)) = some (slots (b.word 256 hash)) := by
  have performed : modifyMany clear ([a, a].map (Solidity.Storage.Loc.word 256 hash)) slots =
      some (TypeGraph.Slots.write (TypeGraph.Slots.write slots (a.word 256 hash) (.prim false))
        (a.word 256 hash) (.prim false)) := rfl
  rw [performed]
  exact congrArg some (resolved_family_outside hash_lt (by decide) (by decide) fits placed
    [(pathA, 0), (pathA, 0)] [a, a] rfl pathB 0 b rfl regions (by decide)
    slots _ clear performed)

/-- info: 'Solidity.Backend.StorageOps.LayoutAccess.resolve_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resolve_bounded
/-- info: 'Solidity.Backend.StorageOps.LayoutAccess.resolveMany_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resolveMany_bounded
/-- info: 'Solidity.Backend.StorageOps.LayoutAccess.resolveMany_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resolveMany_length
/-- info: 'Solidity.Backend.StorageOps.LayoutAccess.resolved_families_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_families_commute
/-- info: 'Solidity.Backend.StorageOps.LayoutAccess.resolved_family_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_family_outside

/-- info: 'Solidity.Backend.StorageOps.LayoutControls.checked_alias_and_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_alias_and_outside
/-- info: 'Solidity.Backend.StorageOps.LayoutControls.checked_alias_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_alias_multiplicity
end Solidity.Backend.StorageOps.LayoutControls
