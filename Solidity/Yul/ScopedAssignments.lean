import Solidity.Yul.AssignmentCheck
import Solidity.Yul.ScopedExpressions

/-!
# Scoped assignments over the existing intrinsic assignment judgement

Targets use ScopedNames.targetEnv: structured paths resolve against the original
declarations before function projection. RHS expressions use the constructed
readEnv plus ScopedExpressions' independent namespace property. Local/function
table coherence, lexical validity, Source occurrence/ID attachment, policy,
physical writeback and dirty-word execution are separate obligations.
-/
namespace Solidity.Yul.ScopedAssignments
open Solidity.Source (Syn)

/-- Recover the exact existing RHS derivation without elaborating it again. -/
def rhsD {F X n reads writes paths rhs}
    (d : @AssignmentD F X n reads writes paths rhs) : ExprD reads rhs paths.length := by
  cases d with
  | intro _ _ _ expression => exact expression

def targetsD {F X n reads writes paths rhs}
    (d : @AssignmentD F X n reads writes paths rhs) : TargetsD writes paths := by
  cases d with
  | intro _ _ targets _ => exact targets

/-- This property concerns external targets only. A local target has no external
reference; True does not assert that its supplied name is lexically valid. -/
def TargetCorrect {root X n decls} (scope : ExternalScope root X)
    (locals : List (String × Fin n)) {name parts target}
    (d : TargetD (ScopedNames.targetEnv decls scope locals) name parts target) : Prop := by
  apply TargetD.casesOn (motive := fun _ _ _ => Prop) d
  case «local» => intros; exact True
  case external =>
    intro parts ref priority resolution
    exact Nonempty (ScopedExternalD decls scope true name parts ref)

theorem target_scoped {root X n decls} (scope : ExternalScope root X)
    (locals : List (String × Fin n)) {name parts target}
    (d : TargetD (ScopedNames.targetEnv decls scope locals) name parts target) :
    TargetCorrect scope locals d := by
  apply TargetD.casesOn (motive := fun parts target d =>
    TargetCorrect scope locals d) d
  case «local» => intros; exact True.intro
  case external =>
    intro parts ref priority resolution
    exact ScopedNames.target_derivation_scoped locals (.external priority resolution)

def PathCorrect {root X n decls} (scope : ExternalScope root X)
    (locals : List (String × Fin n)) {path target}
    (d : TargetPathD (ScopedNames.targetEnv decls scope locals) path target) : Prop := by
  refine TargetPathD.casesOn (motive := fun _ _ _ => Prop) d ?_
  intro head tail target targetD
  exact TargetCorrect scope locals targetD

theorem path_scoped {root X n decls} (scope : ExternalScope root X)
    (locals : List (String × Fin n)) {path target}
    (d : TargetPathD (ScopedNames.targetEnv decls scope locals) path target) :
    PathCorrect scope locals d := by
  cases d with
  | path targetD => exact target_scoped scope locals targetD

def TargetsCorrect {root X n decls} (scope : ExternalScope root X)
    (locals : List (String × Fin n)) {paths}
    (d : TargetsD (ScopedNames.targetEnv decls scope locals) paths) : Prop := by
  apply TargetsD.casesOn (motive := fun _ _ => Prop) d
  case nil => exact True
  case cons =>
    intro path rest target head tail
    exact PathCorrect scope locals head ∧ TargetsCorrect scope locals tail
termination_by structural d

theorem targets_scoped {root X n decls} (scope : ExternalScope root X)
    (locals : List (String × Fin n)) {paths}
    (d : TargetsD (ScopedNames.targetEnv decls scope locals) paths) :
    TargetsCorrect scope locals d := by
  apply TargetsD.casesOn (motive := fun paths d => TargetsCorrect scope locals d) d
  case nil => exact True.intro
  case cons =>
    intro path rest target head tail
    exact ⟨path_scoped scope locals head, targets_scoped scope locals tail⟩
termination_by structural d

/-- The independent extra condition is on the SAME actual RHS derivation.
Target scopedness is derived unconditionally below from the structured target
environment, rather than asserted as an extra preparation premise. -/
def Correct {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {paths rhs}
    (d : AssignmentD (input.readEnv scope locals functions)
      (ScopedNames.targetEnv decls scope locals) paths rhs) : Prop :=
  ScopedExpressions.CorrectExpr input scope locals functions (rhsD d)

theorem correct_targets {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {paths rhs}
    (d : AssignmentD (input.readEnv scope locals functions)
      (ScopedNames.targetEnv decls scope locals) paths rhs) :
    TargetsCorrect scope locals (targetsD d) :=
  targets_scoped scope locals (targetsD d)

structure Checked {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (paths : List (List String))
    (rhs : Syn .yulExpr) : Type where
  typed : AssignmentD (input.readEnv scope locals functions)
    (ScopedNames.targetEnv decls scope locals) paths rhs
  correct : Correct input scope locals functions typed

def Checked.statement {root X F n decls input scope locals functions paths rhs}
    (certificate : @Checked root X F n decls input scope locals functions paths rhs)
    (control : Control) : Stmt F X control n :=
  certificate.typed.statement control

/-- Run the actual existing assignment checker, then certify scoped RHS
resolution. The empty CURRENT context has the same proved fast path as
ScopedExpressions; a nonempty original namespace may project to that context. -/
def check {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (paths : List (List String)) (rhs : Syn .yulExpr) :
    Option (Checked input scope locals functions paths rhs) :=
  match checkAssignment (input.readEnv scope locals functions)
      (ScopedNames.targetEnv decls scope locals) paths rhs with
  | none => none
  | some typed =>
    if empty : X = [] then
      have noMembers : ∀ ty, Member X ty → False := by
        cases empty
        intro ty index
        cases index
      some ⟨typed, ScopedExpressions.correctExpr_noMembers input scope locals functions
        noMembers (rhsD typed)⟩
    else
      letI : Decidable (Correct input scope locals functions typed) :=
        ScopedExpressions.decideExpr input scope locals functions (rhsD typed)
      if correct : Correct input scope locals functions typed then
        some ⟨typed, correct⟩
      else none

theorem Checked.complete {root X F n decls input scope locals functions paths rhs}
    (certificate : @Checked root X F n decls input scope locals functions paths rhs) :
    check input scope locals functions paths rhs = some certificate := by
  cases certificate with
  | mk typed correct =>
    unfold check
    rw [typed.complete]
    change (if empty : X = [] then
      some ⟨typed, ScopedExpressions.correctExpr_noMembers input scope locals functions
        (by cases empty; intro ty index; cases index) (rhsD typed)⟩
      else
        letI : Decidable (Correct input scope locals functions typed) :=
        ScopedExpressions.decideExpr input scope locals functions (rhsD typed)
        if good : Correct input scope locals functions typed then some ⟨typed, good⟩ else none :
      Option (Checked input scope locals functions paths rhs)) = _
    split <;> rfl

theorem check_iff {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (paths : List (List String)) (rhs : Syn .yulExpr) :
    (check input scope locals functions paths rhs).isSome = true ↔
      Nonempty (Checked input scope locals functions paths rhs) := by
  constructor
  · intro h
    cases actual : check input scope locals functions paths rhs with
    | none => rw [actual] at h; cases h
    | some certificate => exact ⟨certificate⟩
  · rintro ⟨certificate⟩
    rw [certificate.complete]
    rfl

/-- Concrete old-checker erasure for empty current contexts, including a
nonempty original namespace. No assumed checker or state agreement premise. -/
theorem closed_erasure {root F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root []) (locals : List (String × Fin n))
    (functions : FunctionNames F) (paths : List (List String)) (rhs : Syn .yulExpr) :
    (check input scope locals functions paths rhs).map Checked.typed =
      checkAssignment (input.readEnv scope locals functions)
        (ScopedNames.targetEnv decls scope locals) paths rhs := by
  unfold check
  cases actual : checkAssignment (input.readEnv scope locals functions)
      (ScopedNames.targetEnv decls scope locals) paths rhs with
  | none => rfl
  | some typed => rfl


/-- Function external contexts expose only readonly global references. Thus
every actual variable-assignment target is local; world-effect builtins are
outside this theorem and are not ruled out. -/
theorem function_target_local {root X n decls} (parent : ExternalScope root X)
    (locals : List (String × Fin n)) {name parts target}
    (d : TargetD (ScopedNames.targetEnv decls (.function parent) locals) name parts target) :
    ∃ index : Fin n, target = .local index := by
  cases d with
  | «local» binding => exact ⟨_, rfl⟩
  | external priority resolution =>
      obtain ⟨certificate⟩ := ScopedNames.target_derivation_scoped locals
        (TargetD.external priority resolution)
      exact False.elim certificate.function_noWrites

theorem function_targets_local {root X n decls} (parent : ExternalScope root X)
    (locals : List (String × Fin n)) {paths}
    (d : TargetsD (ScopedNames.targetEnv decls (.function parent) locals) paths) :
    ∀ position, ∃ index : Fin n, d.terms position = .local index := by
  induction d with
  | nil => exact fun position => Fin.elim0 position
  | cons head tail ih =>
      intro position
      refine Fin.cases ?_ (fun previous => ?_) position
      · cases head with
        | path targetD => exact function_target_local parent locals targetD
      · exact ih previous

/-- An accepted certificate retains the ACTUAL old assignment result in every
context. This is checker erasure, not a Source execution refinement theorem. -/
theorem Checked.old_result {root X F n decls input scope locals functions paths rhs}
    (certificate : @Checked root X F n decls input scope locals functions paths rhs) :
    checkAssignment (input.readEnv scope locals functions)
      (ScopedNames.targetEnv decls scope locals) paths rhs = some certificate.typed :=
  certificate.typed.complete

end Solidity.Yul.ScopedAssignments
