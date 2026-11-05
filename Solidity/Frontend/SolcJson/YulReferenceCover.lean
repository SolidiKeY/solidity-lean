import Solidity.Frontend.SolcJson.YulOccurrenceCollect

/-! Unique forward accounting for PROVIDED typed metadata references, using
actual AST occurrence/role derivations. This does not identify which uncovered
AST identifiers require external metadata; backward/free-reference accounting,
Source namespace provenance and admission remain separate obligations. -/
namespace Solidity.Frontend.YulJson.ReferenceCover
open Lean (Json)
open Solidity.Yul
open Occurrences

structure Candidate {X} (table : DeclarationTable X) (original : Names.Original)
    (root : Json) (reference : Reference table) where
  occurrence : Occurrence root false
  attachment : ReferenceAttachment.Attached table original
    occurrence.write occurrence.node reference

def candidate {X table original root} (reference : @Reference X table)
    (occurrence : Occurrence root false) : Option (Candidate table original root reference) :=
  (ReferenceAttachment.check table original occurrence.write occurrence.node reference).toOption.map
    (fun attachment => ⟨occurrence,attachment⟩)

theorem Candidate.complete {X table original root reference}
    (entry : @Candidate X table original root reference) :
    candidate reference entry.occurrence = some entry := by
  cases entry with
  | mk occurrence attachment =>
      unfold candidate
      rw [attachment.complete]
      rfl

theorem Candidate.eq_of_path_eq {X table original root reference}
    (one two : @Candidate X table original root reference)
    (same : one.occurrence.path = two.occurrence.path) : one = two := by
  have occurrenceEq := one.occurrence.eq_of_path_eq two.occurrence same
  cases one with
  | mk occurrence attachment =>
      cases two with
      | mk other otherAttachment =>
          dsimp only at occurrenceEq
          cases occurrenceEq
          have sameAttachment : attachment = otherAttachment :=
            Except.ok.inj (attachment.complete.symm.trans otherAttachment.complete)
          cases sameAttachment
          rfl

instance {X table original root reference} :
    DecidableEq (@Candidate X table original root reference) := fun one two =>
  if same : one.occurrence.path = two.occurrence.path then
    isTrue (one.eq_of_path_eq two same)
  else isFalse (fun equal => same (congrArg (fun entry => entry.occurrence.path) equal))

/-- Normalize duplicate enumeration of the SAME actual position only.
Distinct positions with identical JSON or source spans remain distinct. -/
def dedup {X table original root reference} :
    List (@Candidate X table original root reference) →
      List (Candidate table original root reference)
  | [] => []
  | first::rest =>
      let remaining := dedup rest
      if first ∈ remaining then remaining else first::remaining

theorem dedup_mem {X table original root reference}
    (entries : List (@Candidate X table original root reference)) :
    ∀ entry, entry ∈ dedup entries ↔ entry ∈ entries := by
  induction entries with
  | nil => intro entry; rfl
  | cons first rest ih =>
      intro entry
      rw [dedup]
      split
      · next present =>
          constructor
          · intro member; exact List.mem_cons_of_mem first ((ih entry).mp member)
          · intro member
            rcases List.mem_cons.mp member with same | member
            · subst entry; exact present
            · exact (ih entry).mpr member
      · simp only [List.mem_cons,ih entry]

theorem dedup_nodup {X table original root reference}
    (entries : List (@Candidate X table original root reference)) : (dedup entries).Nodup := by
  induction entries with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
      rw [dedup]
      split
      · exact ih
      · next absent => exact List.nodup_cons.mpr ⟨absent,ih⟩

def candidates {X table original root} (collected : Collected root false)
    (reference : @Reference X table) : List (Candidate table original root reference) :=
  dedup (collected.occurrences.filterMap (candidate (original := original) reference))

/-- Every independently attached actual occurrence is in the concrete list.
The collector supplies its real coverage proof, not a caller simulation law. -/
theorem candidate_mem {X table original root reference} (collected : Collected root false)
    (entry : @Candidate X table original root reference) :
    entry ∈ candidates collected reference := by
  obtain ⟨found,member,pathEq,_,_⟩ := collected.complete entry.occurrence.derivation
  have same : found = entry.occurrence := found.eq_of_path_eq entry.occurrence pathEq
  cases same
  apply (dedup_mem _ entry).mpr
  exact List.mem_filterMap.mpr ⟨entry.occurrence,member,entry.complete⟩

structure Unique {X} (table : DeclarationTable X) (original : Names.Original)
    (root : Json) (reference : Reference table) where
  entry : Candidate table original root reference
  unique : ∀ other : Candidate table original root reference,
    other.occurrence.path = entry.occurrence.path

inductive Error where
  | missing
  | ambiguous
  deriving Repr, DecidableEq

def check {X table original root} (collected : Collected root false)
    (reference : @Reference X table) : Except Error (Unique table original root reference) :=
  match found : candidates collected reference with
  | [] => .error .missing
  | [entry] => .ok ⟨entry,by
      intro other
      have member := candidate_mem collected other
      rw [found] at member
      have same : other = entry := List.mem_singleton.mp member
      exact congrArg (fun matched => matched.occurrence.path) same⟩
  | _::_::_ => .error .ambiguous

/-- Exact completeness against independent unique ACTUAL occurrence attachment.
Redundant supplied enumeration does not weaken this theorem: only equal paths
are normalized, with node and role determinism already proved. -/
theorem Unique.complete {X table original root reference}
    (unique : @Unique X table original root reference) (collected : Collected root false) :
    check (original := original) collected reference = .ok unique := by
  cases unique with
  | mk entry uniqueness =>
      have member := candidate_mem collected entry
      unfold check
      split
      · next found => rw [found] at member; cases member
      · next other found =>
          rw [found] at member
          have same : entry = other := List.mem_singleton.mp member
          cases same
          rfl
      · next first second rest found =>
          have same : first = second := first.eq_of_path_eq second
            ((uniqueness first).trans (uniqueness second).symm)
          have nodup := dedup_nodup
            (collected.occurrences.filterMap (candidate (original := original) reference))
          change (candidates collected reference).Nodup at nodup
          rw [found] at nodup
          have absent := (List.nodup_cons.mp nodup).1
          apply False.elim
          apply absent
          rw [same]
          exact List.mem_cons_self

theorem check_iff {X table original root} (collected : Collected root false)
    (reference : @Reference X table) :
    (check (original := original) collected reference).isOk = true ↔ Nonempty (Unique table original root reference) := by
  constructor
  · intro valid
    cases actual : check (original := original) collected reference with
    | error reason => rw [actual] at valid; cases valid
    | ok result => exact ⟨result⟩
  · rintro ⟨unique⟩
    rw [unique.complete collected]
    rfl

/-- Every PROVIDED metadata reference has exactly one actual AST position.
The list index prevents omitting or substituting a different declaration. -/
inductive All {X} (table : DeclarationTable X) (original : Names.Original) (root : Json) :
    List (Reference table) → Type where
  | nil : All table original root []
  | cons {reference rest} : Unique table original root reference →
      All table original root rest → All table original root (reference::rest)

inductive AllError where
  | at (index : Nat) (reason : Error)
  deriving Repr

def checkAll {X table original root} (collected : Collected root false) :
    (references : List (@Reference X table)) →
      Except AllError (All table original root references)
  | [] => .ok .nil
  | reference::rest => do
      let first ← (check (original := original) collected reference).mapError (AllError.at 0)
      let remaining ← (checkAll collected rest).mapError
        (fun error => match error with | .at index reason => .at (index+1) reason)
      pure (.cons first remaining)

theorem All.complete {X table original root references}
    (all : @All X table original root references) (collected : Collected root false) :
    checkAll collected references = .ok all := by
  induction all with
  | nil => rfl
  | cons first remaining ih =>
      simp only [checkAll,first.complete collected,ih,bind,Except.bind,
        Except.mapError,pure,Except.pure]

theorem checkAll_iff {X table original root} (collected : Collected root false)
    (references : List (@Reference X table)) :
    (checkAll (original := original) collected references).isOk = true ↔
      Nonempty (All table original root references) := by
  constructor
  · intro valid
    cases actual : checkAll (original := original) collected references with
    | error reason => rw [actual] at valid; cases valid
    | ok result => exact ⟨result⟩
  · rintro ⟨all⟩
    rw [all.complete collected]
    rfl

def All.get {X table original root references}
    (all : @All X table original root references) :
    (index : Fin references.length) → Unique table original root (references.get index) := by
  apply All.casesOn (motive := fun references _ =>
    (index : Fin references.length) → Unique table original root (references.get index)) all
  case nil => exact fun index => Fin.elim0 index
  case cons =>
    intro reference rest first remaining
    exact fun index => Fin.cases first (fun index => remaining.get index) index
termination_by structural all

end Solidity.Frontend.YulJson.ReferenceCover
