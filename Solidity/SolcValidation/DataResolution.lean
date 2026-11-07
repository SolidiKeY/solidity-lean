import Solidity.SolcValidation.DataLayout

/-!
# Unique object-data resolution

A checked per-object table resolves a present label to its exact reference,
not merely to some reference. Compiler/path association remains separate.
-/
namespace Solidity.SolcValidation

private theorem references_unique {artifact : List DataByte} {label : String}
    {entries : List (String × DataRef artifact)}
    (unique : (entries.map Prod.fst).Nodup)
    {left right : DataRef artifact}
    (leftMember : (label, left) ∈ entries) (rightMember : (label, right) ∈ entries) :
    left = right := by
  induction entries with
  | nil => cases leftMember
  | cons entry rest ih =>
      obtain ⟨name, ref⟩ := entry
      have parts : name ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup :=
        List.nodup_cons.mp unique
      rcases List.mem_cons.mp leftMember with leftHead | leftTail
      · rcases List.mem_cons.mp rightMember with rightHead | rightTail
        · exact (congrArg Prod.snd leftHead).trans (congrArg Prod.snd rightHead).symm
        · have labels : label = name := congrArg Prod.fst leftHead
          have present : label ∈ rest.map Prod.fst := List.mem_map.mpr ⟨_, rightTail, rfl⟩
          exact False.elim (parts.1 (labels ▸ present))
      · rcases List.mem_cons.mp rightMember with rightHead | rightTail
        · have labels : label = name := congrArg Prod.fst rightHead
          have present : label ∈ rest.map Prod.fst := List.mem_map.mpr ⟨_, leftTail, rfl⟩
          exact False.elim (parts.1 (labels ▸ present))
        · exact ih parts.2 leftTail rightTail

/-- The intrinsic uniqueness invariant rules out competing references for one
label in this table. It does not associate that label with a source object. -/
theorem DataTable.selection_unique {artifact : List DataByte}
    (table : DataTable artifact) {label : String}
    (left right : DataSelection table.entries label) : left.ref = right.ref :=
  references_unique table.unique left.member right.member

/-- Membership certificates are proof-irrelevant; reference equality determines
selection equality. No equality decision procedure for references is assumed. -/
theorem DataSelection.ext {artifact : List DataByte}
    {entries : List (String × DataRef artifact)} {label : String}
    (left right : DataSelection entries label) (same : left.ref = right.ref) :
    left = right := by
  cases left with
  | mk leftRef leftMember =>
      cases right with
      | mk rightRef rightMember =>
          cases same
          rfl

/-- Every supplied membership witness in a unique table is reproduced exactly
by the actual resolver, rather than only yielding a successful status bit. -/
theorem DataTable.select_complete {artifact : List DataByte}
    (table : DataTable artifact) {label : String}
    (selected : DataSelection table.entries label) :
    table.select label = some selected := by
  have present : (table.select label).isSome = true := selectData_complete selected
  cases actual : table.select label with
  | none => simp only [actual, Option.isSome_none, Bool.false_eq_true] at present
  | some result =>
      exact congrArg some (DataSelection.ext result selected (table.selection_unique result selected))

/-- Missing names fail and present names succeed; there is no fallback entry. -/
theorem DataTable.select_iff {artifact : List DataByte}
    (table : DataTable artifact) (label : String) :
    (table.select label).isSome = true ↔ ∃ ref, (label, ref) ∈ table.entries := by
  constructor
  · intro present
    cases actual : table.select label with
    | none => simp only [actual, Option.isSome_none, Bool.false_eq_true] at present
    | some selected => exact ⟨selected.ref, selected.member⟩
  · rintro ⟨ref, member⟩
    exact selectData_complete ⟨ref, member⟩

end Solidity.SolcValidation
