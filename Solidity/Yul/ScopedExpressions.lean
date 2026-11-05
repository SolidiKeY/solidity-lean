import Solidity.Yul.ScopedNames

/-!
# Supplemental scoped correctness of existing expression derivations

This reuses the existing arity/context-indexed ExprD/ArgsD. The property ONLY
concerns external namespace resolution. Literal/local clauses contain no external
reference; they do not assert lexical validity, Source provenance or coverage.
Callee bodies, local/function-table validity, Source occurrence6578 and physical/
dirty execution remain separate. The environment is the actual constructed readEnv.
-/
namespace Solidity.Yul.ScopedExpressions
open Solidity.Source (Syn)
open Solidity.Yul.ScopedNames

mutual
def CorrectExpr {root X F n decls} (checked : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {term arity}
    (d : ExprD (checked.readEnv scope locals functions) term arity) : Prop := by
  apply ExprD.casesOn (motive_1 := fun _ _ _ => Prop) d
  case literal => intros; exact True
  case «variable» => intros; exact True
  case external =>
    intro name parts ref priority binding
    exact Nonempty (ScopedExternalD decls scope false name parts ref)
  case builtin =>
    intro name args a r builtin spelling arguments
    exact CorrectArgs checked scope locals functions arguments
  case call =>
    intro name args sig function noBuiltin binding arguments
    exact CorrectArgs checked scope locals functions arguments
termination_by structural d

def CorrectArgs {root X F n decls} (checked : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {terms arity}
    (d : ArgsD (checked.readEnv scope locals functions) terms arity) : Prop := by
  apply ArgsD.casesOn (motive_2 := fun _ _ _ => Prop) d
  case nil => exact True
  case cons =>
    intro first rest count head tail
    exact CorrectExpr checked scope locals functions head ∧
      CorrectArgs checked scope locals functions tail
termination_by structural d
end

mutual
def decideExpr {root X F n decls} (checked : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {term arity}
    (d : ExprD (checked.readEnv scope locals functions) term arity) :
    Decidable (CorrectExpr checked scope locals functions d) := by
  apply ExprD.casesOn (motive_1 := fun _ _ d =>
    Decidable (CorrectExpr checked scope locals functions d)) d
  case literal => intros; exact isTrue True.intro
  case «variable» => intros; exact isTrue True.intro
  case external =>
    intro name parts ref priority binding
    exact if canonical : ExternalKeys.NoDot name then
      isTrue (ScopedNames.lookup_sound checked.canonical canonical (resolve_complete binding))
    else isFalse (fun correct => by
      obtain ⟨certificate⟩ := correct
      exact canonical (checked.canonical name (ScopedNames.scoped_name_mem certificate)))
  case builtin =>
    intro name args a r builtin spelling arguments
    exact decideArgs checked scope locals functions arguments
  case call =>
    intro name args sig function noBuiltin binding arguments
    exact decideArgs checked scope locals functions arguments
termination_by structural d

def decideArgs {root X F n decls} (checked : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {terms arity}
    (d : ArgsD (checked.readEnv scope locals functions) terms arity) :
    Decidable (CorrectArgs checked scope locals functions d) := by
  apply ArgsD.casesOn (motive_2 := fun _ _ d =>
    Decidable (CorrectArgs checked scope locals functions d)) d
  case nil => exact isTrue True.intro
  case cons =>
    intro first rest count head tail
    let headDecision := decideExpr checked scope locals functions head
    let tailDecision := decideArgs checked scope locals functions tail
    exact @instDecidableAnd _ _ headDecision tailDecision
termination_by structural d
end


mutual
/-- A real empty-current-context premise, not an original-root assumption. -/
theorem correctExpr_noMembers {root X F n decls} (checked : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (empty : ∀ ty, Member X ty → False) {term arity}
    (d : ExprD (checked.readEnv scope locals functions) term arity) :
    CorrectExpr checked scope locals functions d := by
  apply ExprD.casesOn (motive_1 := fun _ _ d =>
    CorrectExpr checked scope locals functions d) d
  case literal => intros; exact True.intro
  case «variable» => intros; exact True.intro
  case external =>
    intro name parts ref priority binding
    exact False.elim (empty _ ref.index)
  case builtin =>
    intro name args a r builtin spelling arguments
    exact correctArgs_noMembers checked scope locals functions empty arguments
  case call =>
    intro name args sig function noBuiltin binding arguments
    exact correctArgs_noMembers checked scope locals functions empty arguments
termination_by structural d

theorem correctArgs_noMembers {root X F n decls} (checked : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (empty : ∀ ty, Member X ty → False) {terms arity}
    (d : ArgsD (checked.readEnv scope locals functions) terms arity) :
    CorrectArgs checked scope locals functions d := by
  apply ArgsD.casesOn (motive_2 := fun _ _ d =>
    CorrectArgs checked scope locals functions d) d
  case nil => exact True.intro
  case cons =>
    intro first rest count head tail
    exact ⟨correctExpr_noMembers checked scope locals functions empty head,
      correctArgs_noMembers checked scope locals functions empty tail⟩
termination_by structural d
end

structure Checked {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (term : Syn .yulExpr) : Type where
  arity : Nat
  typed : ExprD (input.readEnv scope locals functions) term arity
  correct : CorrectExpr input scope locals functions typed

def Checked.toTyped {root X F n decls input scope locals functions term}
    (c : @Checked root X F n decls input scope locals functions term) :
    ((arity : Nat) × ExprD (input.readEnv scope locals functions) term arity) :=
  ⟨c.arity, c.typed⟩

def Checked.term {root X F n decls input scope locals functions term}
    (c : @Checked root X F n decls input scope locals functions term) : Expr F X n c.arity :=
  c.typed.term

/-- Reuse the ACTUAL expression checker and postcheck its independent scope
property. The current-X empty branch constructs a proved certificate without
walking the derivation again. Neither branch changes the old typed term. -/
def check {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (term : Syn .yulExpr) :
    Option (Checked input scope locals functions term) :=
  match inferExpr (input.readEnv scope locals functions) term with
  | none => none
  | some ⟨arity, typed⟩ =>
    if empty : X = [] then
      have noMembers : ∀ ty, Member X ty → False := by
        cases empty
        intro ty index
        cases index
      some ⟨arity, typed, correctExpr_noMembers input scope locals functions noMembers typed⟩
    else
      letI := decideExpr input scope locals functions typed
      if correct : CorrectExpr input scope locals functions typed then
        some ⟨arity, typed, correct⟩
      else none

theorem Checked.complete {root X F n decls input scope locals functions term}
    (c : @Checked root X F n decls input scope locals functions term) :
    check input scope locals functions term = some c := by
  cases c with
  | mk arity typed correct =>
      unfold check
      rw [typed.complete]
      change (if empty : X = [] then
        some ⟨arity, typed, correctExpr_noMembers input scope locals functions
          (by cases empty; intro ty index; cases index) typed⟩
        else
          letI := decideExpr input scope locals functions typed
          if good : CorrectExpr input scope locals functions typed then
            some ⟨arity, typed, good⟩ else none :
          Option (Checked input scope locals functions term)) = _
      split
      · rfl
      · rfl

theorem check_iff {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (term : Syn .yulExpr) :
    (check input scope locals functions term).isSome = true ↔
      Nonempty (Checked input scope locals functions term) := by
  constructor
  · intro h
    cases actual : check input scope locals functions term with
    | none => rw [actual] at h; cases h
    | some c => exact ⟨c⟩
  · rintro ⟨c⟩
    rw [c.complete]
    rfl

/-- Concrete closed-instance erasure, including an original nonempty namespace
projected to an empty current context. No assumed checker agreement is used. -/
theorem closed_erasure {root F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root []) (locals : List (String × Fin n))
    (functions : FunctionNames F) (term : Syn .yulExpr) :
    (check input scope locals functions term).map Checked.toTyped =
      inferExpr (input.readEnv scope locals functions) term := by
  unfold check
  cases actual : inferExpr (input.readEnv scope locals functions) term with
  | none => rfl
  | some pair => cases pair; rfl

end Solidity.Yul.ScopedExpressions
