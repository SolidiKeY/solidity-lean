import Solidity.Source.Syntax

/-!
Generic control correspondence over the existing intrinsic `Syn category`.
The parser, profile observation, and tag observation are parameters: this
module introduces no alternative AST and evaluates no finite parser table.
-/
namespace Solidity.Frontend.GenericSourceControls
open Solidity.Source

/-- The exact Boolean control shape used by statement grammar fixtures. -/
def check {ε Tag : Type} [BEq Tag] {category : Cat}
    (result : Except ε (Syn category)) (accepts profile : Bool)
    (required : List Tag) (inProfile : Syn category → Bool)
    (tags : Syn category → List Tag) : Bool :=
  match result with
  | .error _ => !accepts
  | .ok tree => accepts && (inProfile tree == profile) &&
      required.all (fun tag => (tags tree).contains tag)

/-- A source-level semantic observation retaining the typed accepted tree.
Refusal is required for negative controls; profile and required tags are
observed only for accepted trees, exactly as in the original checker. -/
def Specification {ε Tag : Type} {category : Cat}
    (result : Except ε (Syn category)) (accepts profile : Bool)
    (required : List Tag) (inProfile : Syn category → Bool)
    (tags : Syn category → List Tag) : Prop :=
  match result with
  | .error _ => accepts = false
  | .ok tree => (accepts = true ∧ inProfile tree = profile) ∧
      ∀ tag ∈ required, tag ∈ tags tree

/-- Parameterized semantic correspondence; no finite `decide` proof. -/
theorem check_iff {ε Tag : Type} [BEq Tag] [LawfulBEq Tag] {category : Cat}
    (result : Except ε (Syn category)) (accepts profile : Bool)
    (required : List Tag) (inProfile : Syn category → Bool)
    (tags : Syn category → List Tag) :
    check result accepts profile required inProfile tags = true ↔
      Specification result accepts profile required inProfile tags := by
  cases result with
  | error e =>
    cases accepts with
    | false => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | true => constructor <;> intro h <;> cases h
  | ok tree =>
    simp only [check, Specification, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true, List.contains_iff_mem]

/-- A negative fixture cannot pass by observing an accepted tree. -/
theorem negative_requires_refusal {ε Tag : Type} [BEq Tag] {category : Cat}
    (result : Except ε (Syn category)) (profile : Bool) (required : List Tag)
    (inProfile : Syn category → Bool) (tags : Syn category → List Tag)
    (h : check result false profile required inProfile tags = true) :
    ∃ e : ε, result = .error e := by
  cases result with
  | error e => exact ⟨e, rfl⟩
  | ok tree =>
    simp only [check, Bool.false_and, Bool.false_eq_true] at h

/-- A typed table row reuses a fixture of any existing type and its exact
checker proposition. It adds evidence without copying the fixture schema. -/
structure Row (Fixture : Type) (checker : Fixture → Bool) where
  fixture : Fixture
  checked : checker fixture = true

/-- Every row exposes precisely its original checker proposition. -/
theorem row_checked {Fixture : Type} {checker : Fixture → Bool}
    (row : Row Fixture checker) : checker row.fixture = true := row.checked

#print axioms check_iff
#print axioms negative_requires_refusal
#print axioms row_checked
end Solidity.Frontend.GenericSourceControls
