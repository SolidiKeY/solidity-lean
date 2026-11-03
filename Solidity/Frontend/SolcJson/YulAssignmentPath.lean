import Solidity.Frontend.SolcJson.YulTargetPath

/-! Actual assignment RHS read positions and original admitted-assignment
composition. This observes existing indexed derivations, not a new AST.
Whole-block/backward/provenance alignment remains separate. -/
namespace Solidity.Frontend.YulJson.AssignmentPath
open Lean (Json)
open Solidity.Yul

inductive Link : TypingLeaves.Path → List Occurrences.Edge → Prop where
  | value {source child} (ordinal : Nat) : ExpressionPath.Link source child →
      Link source (.field "value" ordinal::child)

theorem Link.json_injective {first second jsonPath}
    (one : Link first jsonPath) (two : Link second jsonPath) : first = second := by
  cases one with
  | value ordinal route =>
      cases two with
      | value otherOrdinal otherRoute => exact route.json_injective otherRoute

def At {F X n E} (node : Json) (entry : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) : Prop :=
  ∃ jsonPath found, Link entry.1 jsonPath ∧
    Occurrences.OccurrenceD node false jsonPath false found ∧
    identifierPath found = .ok (entry.2.name,entry.2.parts)

/-- The actual assignment field/tag facts transport an exact read witness,
including the actual object ordinal, with the actual RHS read role. -/
theorem value_positions {F X n E node value rhs arity}
    (kind : string node "nodeType" = .ok "YulAssignment")
    (valueEq : field node "value" = .ok value)
    (typed : @ExprD F X n E rhs arity)
    (positions : TypingLeaves.All (fun path leaf => ExpressionPath.At value (path,leaf))
      (TypingLeaves.reads typed [])) :
    TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.reads typed []) := by
  intro entry present
  obtain ⟨path,found,linked,occurrence,spelled⟩ := positions entry present
  have kindEq := ObjectLookup.kind_of_string kind
  have notIdentifier : Occurrences.isIdentifier node = false := by
    simp only [Occurrences.isIdentifier,kindEq]
    decide +kernel
  have selected : Occurrences.includeField node "value" = true := by
    simp only [Occurrences.includeField,kindEq,Occurrences.childKeys]
    decide +kernel
  have role : Occurrences.fieldRole node "value" = false := by
    simp only [Occurrences.fieldRole,kindEq]
    decide +kernel
  obtain ⟨ordinal,lifted⟩ := ObjectLookup.field_occurrence (start := false)
    valueEq notIdentifier selected (by simpa only [role] using occurrence)
  exact ⟨.field "value" ordinal::path,found,.value ordinal linked,lifted,spelled⟩

/-- All RHS positions from the ACTUAL original successful statement decoder
and the exact existing expression typing derivation. -/
theorem decoded_reads {F X n E} (fuel : Nat) {node first rest rhs arity}
    (parsed : statementAux fuel node = .ok (.yulAssign first rest rhs))
    (typed : @ExprD F X n E rhs arity) :
    TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.reads typed []) := by
  obtain ⟨childFuel,_,kind,values,pairs,value,_,_,_,valueEq,expressionEq⟩ :=
    TargetPath.decoded_assignment_fields fuel parsed
  exact value_positions kind valueEq typed (ExpressionPath.decoded_paths childFuel expressionEq typed)

structure Witness {F X n E} (node : Json)
    (entry : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) where
  path : List Occurrences.Edge
  found : Json
  linked : Link entry.1 path
  occurrence : Occurrences.OccurrenceD node false path false found
  spelled : identifierPath found = .ok (entry.2.name,entry.2.parts)

theorem At.witness {F X n E node entry} (actual : @At F X n E node entry) :
    Nonempty (Witness node entry) := by
  obtain ⟨path,found,linked,occurrence,spelled⟩ := actual
  exact ⟨⟨path,found,linked,occurrence,spelled⟩⟩

theorem Witness.position_unique {F X n E node first second}
    (one : @Witness F X n E node first) (two : Witness node second)
    (same : one.path = two.path) : first = second := by
  have pathEq : first.1 = second.1 := one.linked.json_injective (same ▸ two.linked)
  have nodeEq : one.found = two.found :=
    (one.occurrence.deterministic two.occurrence same).2
  have spellingEq : (first.2.name,first.2.parts) = (second.2.name,second.2.parts) :=
    Except.ok.inj (one.spelled.symm.trans
      ((congrArg identifierPath nodeEq).trans two.spelled))
  have leafEq : first.2 = second.2 :=
    first.2.spelling_unique second.2 (congrArg Prod.fst spellingEq) (congrArg Prod.snd spellingEq)
  exact Prod.ext pathEq leafEq

/-- Actual RHS reads and LHS writes cannot occupy one JSON position.
This uses original occurrence-role determinism, not disjoint supplied names. -/
theorem Witness.read_write_disjoint {F X n reads writes node readEntry writeEntry}
    (one : @Witness F X n reads node readEntry)
    (two : @TargetPath.Witness X n writes node writeEntry) : one.path ≠ two.path := by
  intro same
  have impossible := (one.occurrence.deterministic two.occurrence same).1
  cases impossible

/-- Concrete read/target composition from SAME original admitted assignment.
The real judgement supplies nonempty/Nodup/RHS arity and original subderivations;
no abstract preparation law is a premise. -/
theorem admitted_positions {F X n reads writes} (fuel : Nat) {node first rest rhs}
    (parsed : statementAux fuel node = .ok (.yulAssign first rest rhs))
    (typed : @AssignmentD F X n reads writes (first::rest) rhs) :
    TypingLeaves.All (fun path leaf => At node (path,leaf))
      (TypingLeaves.reads (ScopedAssignments.rhsD typed) []) ∧
    TypingLeaves.All (fun path leaf => TargetPath.At node (path,leaf))
      (TypingLeaves.targets (ScopedAssignments.targetsD typed) []) :=
  ⟨decoded_reads fuel parsed (ScopedAssignments.rhsD typed),
    TargetPath.decoded_targets fuel parsed (ScopedAssignments.targetsD typed)⟩

end Solidity.Frontend.YulJson.AssignmentPath
