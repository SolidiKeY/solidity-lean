import Solidity.Yul.BlockEnvironment
import Solidity.Yul.ScopedAssignments

/-!
# Concrete scope-indexed block-checker interface

This interface shares the existing closed and scoped expression/assignment
checkers. Its function operation is intrinsic: closed scopes stay closed;
external scopes advance the ORIGINAL scoped namespace and globals context.
No abstract preparation/oracle law, Source state, new program or duplicate
block traversal is introduced. Whole-block generalization remains separate.
-/
namespace Solidity.Yul.BlockScope
open Solidity.Source (Syn)
open Solidity.Yul.BlockTyping (Env)

abbrev Fixed {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (term : Syn .yulExpr) (count : Nat) :=
  {checked : ScopedExpressions.Checked input scope locals functions term // checked.arity = count}

def checkFixed {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) (term : Syn .yulExpr) (count : Nat) :
    Option (Fixed input scope locals functions term count) := do
  let checked ← ScopedExpressions.check input scope locals functions term
  if same : checked.arity = count then pure ⟨checked, same⟩ else none

theorem fixed_complete {root X F n decls input scope locals functions term count}
    (certificate : @Fixed root X F n decls input scope locals functions term count) :
    checkFixed input scope locals functions term count = some certificate := by
  rcases certificate with ⟨checked, same⟩
  unfold checkFixed
  rw [checked.complete]
  change (if good : checked.arity = count then
    some (⟨checked, good⟩ : Fixed input scope locals functions term count) else none) = _
  rw [dif_pos same]

def fixedTerm {root X F n decls input scope locals functions term count}
    (certificate : @Fixed root X F n decls input scope locals functions term count) :
    Expr F X n count :=
  certificate.property ▸ certificate.val.term

/-- The empty scope is a concrete closed special case, not an unavailable open
context stub. Both constructors have actual expression/assignment checkers. -/
inductive Scope : List ExternalType → Type where
  | closed : Scope []
  | external {root X decls} (input : @ScopedNames.Checked root decls)
      (original : ExternalScope root X) : Scope X

def Scope.function {X} (scope : Scope X) : Scope (globals X) := by
  apply Scope.casesOn (motive := fun X _ => Scope (globals X)) scope
  case closed => exact .closed
  case external => intro root X decls input original; exact .external input (.function original)

def Scope.reads {X F n} (scope : Scope X) (E : Env F n) : ExprEnv F X n := by
  apply Scope.casesOn (motive := fun X _ => ExprEnv F X n) scope
  case closed => exact E.reads
  case external => intro root X decls input original; exact input.readEnv original E.locals E.functions

def Scope.writes {X F n} (scope : Scope X) (E : Env F n) : TargetEnv X n := by
  apply Scope.casesOn (motive := fun X _ => TargetEnv X n) scope
  case closed => exact E.writes
  case external => intro root X decls input original
                   exact ScopedNames.targetEnv decls original E.locals

/-- The CLOSED case reduces to the original ExprD definition, preserving its
constructor field types rather than wrapping the closed derivation. -/
def ExpressionD {X F n} (scope : Scope X) (E : Env F n)
    (term : Syn .yulExpr) (count : Nat) : Type := by
  apply Scope.casesOn (motive := fun X _ => Type) scope
  case closed => exact ExprD E.reads term count
  case external => intro root X decls input original
                   exact Fixed input original E.locals E.functions term count

def expressionTerm {X F n scope E term count}
    (d : @ExpressionD X F n scope E term count) : Expr F X n count := by
  revert d
  apply Scope.casesOn (motive := fun X scope => ExpressionD scope E term count → Expr F X n count) scope
  case closed => exact fun d => d.term
  case external => intros; exact fixedTerm ‹_›

def checkExpression {X F n} (scope : Scope X) (E : Env F n)
    (term : Syn .yulExpr) (count : Nat) : Option (ExpressionD scope E term count) := by
  apply Scope.casesOn (motive := fun X scope => Option (ExpressionD scope E term count)) scope
  case closed =>
    exact do
      let ⟨arity, typed⟩ ← inferExpr E.reads term
      if same : arity = count then pure (same ▸ typed) else none
  case external => intro root X decls input original
                   exact checkFixed input original E.locals E.functions term count

theorem expression_complete {X F n scope E term count}
    (d : @ExpressionD X F n scope E term count) :
    checkExpression scope E term count = some d := by
  revert d
  apply Scope.casesOn (motive := fun X scope => (d : @ExpressionD X F n scope E term count) →
    checkExpression scope E term count = some d) scope
  case closed =>
    intro d
    change (do
      let ⟨arity, typed⟩ ← inferExpr E.reads term
      if same : arity = count then some (same ▸ typed) else none) = _
    rw [d.complete]
    exact dif_pos rfl
  case external => intro root X decls input original d; exact fixed_complete d

def AssignmentD {X F n} (scope : Scope X) (E : Env F n)
    (paths : List (List String)) (rhs : Syn .yulExpr) : Type := by
  apply Scope.casesOn (motive := fun X _ => Type) scope
  case closed => exact Solidity.Yul.AssignmentD E.reads E.writes paths rhs
  case external => intro root X decls input original
                   exact ScopedAssignments.Checked input original E.locals E.functions paths rhs

def assignmentStatement {X F n scope E paths rhs}
    (d : @AssignmentD X F n scope E paths rhs) (control : Control) : Stmt F X control n := by
  revert d
  apply Scope.casesOn (motive := fun X scope =>
    AssignmentD scope E paths rhs → Stmt F X control n) scope
  case closed => exact fun d => d.statement control
  case external => intro root X decls input original d; exact d.statement control

def checkAssignment {X F n} (scope : Scope X) (E : Env F n)
    (paths : List (List String)) (rhs : Syn .yulExpr) : Option (AssignmentD scope E paths rhs) := by
  apply Scope.casesOn (motive := fun X scope => Option (AssignmentD scope E paths rhs)) scope
  case closed => exact Solidity.Yul.checkAssignment E.reads E.writes paths rhs
  case external => intro root X decls input original
                   exact ScopedAssignments.check input original E.locals E.functions paths rhs

theorem assignment_complete {X F n scope E paths rhs}
    (d : @AssignmentD X F n scope E paths rhs) :
    checkAssignment scope E paths rhs = some d := by
  revert d
  apply Scope.casesOn (motive := fun X scope => (d : @AssignmentD X F n scope E paths rhs) →
    checkAssignment scope E paths rhs = some d) scope
  case closed => intro d; exact d.complete
  case external => intro root X decls input original d; exact d.complete

theorem checkExpression_iff {X F n} (scope : Scope X) (E : Env F n)
    (term : Syn .yulExpr) (count : Nat) :
    (checkExpression scope E term count).isSome = true ↔
      Nonempty (ExpressionD scope E term count) := by
  constructor
  · intro h
    cases actual : checkExpression scope E term count with
    | none => rw [actual] at h; cases h
    | some d => exact ⟨d⟩
  · rintro ⟨d⟩
    rw [expression_complete d]
    rfl

theorem checkAssignment_iff {X F n} (scope : Scope X) (E : Env F n)
    (paths : List (List String)) (rhs : Syn .yulExpr) :
    (checkAssignment scope E paths rhs).isSome = true ↔
      Nonempty (AssignmentD scope E paths rhs) := by
  constructor
  · intro h
    cases actual : checkAssignment scope E paths rhs with
    | none => rw [actual] at h; cases h
    | some d => exact ⟨d⟩
  · rintro ⟨d⟩
    rw [assignment_complete d]
    rfl

end Solidity.Yul.BlockScope
