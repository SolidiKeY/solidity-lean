import Solidity.Yul.TypingLeaves

/-! Preservation of the existing supplemental scoped namespace correctness
through the actual leaf observer. This uses REAL parent certificates, never
assumes a context/namespace-provider law. Source/JSON identity is separate. -/
namespace Solidity.Yul.TypingLeaves
open Solidity.Yul.BlockTyping (Env)
open Solidity.Yul.BlockScope (Scope)
open Solidity.Yul.ScopedExpressions (CorrectExpr CorrectArgs)

mutual
theorem scoped_reads {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {term arity}
    (typed : ExprD (input.readEnv scope locals functions) term arity) (path : Path) :
    CorrectExpr input scope locals functions typed →
      everyRead typed path (fun _ leaf => CorrectExpr input scope locals functions leaf.typed) := by
  revert path
  apply ExprD.casesOn (motive_1 := fun _ _ typed => ∀ path,
    CorrectExpr input scope locals functions typed →
      everyRead typed path (fun _ leaf => CorrectExpr input scope locals functions leaf.typed)) typed
  case literal => intros; exact True.intro
  case «variable» => intros; exact True.intro
  case external =>
    intro name parts reference priority resolved path correct
    exact correct
  case builtin =>
    intro name args a r builtin spelling arguments path correct
    exact scoped_arguments input scope locals functions arguments (path++[.arguments]) correct
  case call =>
    intro name args signature function noBuiltin resolved arguments path correct
    exact scoped_arguments input scope locals functions arguments (path++[.arguments]) correct
termination_by structural typed

theorem scoped_arguments {root X F n decls} (input : @ScopedNames.Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) {terms arity}
    (typed : ArgsD (input.readEnv scope locals functions) terms arity) (path : Path) :
    CorrectArgs input scope locals functions typed →
      everyArgument typed path (fun _ leaf => CorrectExpr input scope locals functions leaf.typed) := by
  revert path
  apply ArgsD.casesOn (motive_2 := fun _ _ typed => ∀ path,
    CorrectArgs input scope locals functions typed →
      everyArgument typed path (fun _ leaf => CorrectExpr input scope locals functions leaf.typed)) typed
  case nil => intros; exact True.intro
  case cons =>
    intro first rest count head tail path correct
    exact ⟨scoped_reads input scope locals functions head (path++[.first]) correct.1,
      scoped_arguments input scope locals functions tail (path++[.rest]) correct.2⟩
termination_by structural typed
end

def emptyNames : ScopedNames.Checked ([] : ExternalNames []) :=
  ⟨by intro name present; cases present⟩

def readCorrect {X F n} (scope : Scope X) (E : Env F n)
    (leaf : ReadLeaf (scope.reads E)) : Prop := by
  revert leaf
  apply Scope.casesOn (motive := fun X scope => ReadLeaf (scope.reads E) → Prop) scope
  case closed => exact fun leaf => CorrectExpr emptyNames .root E.locals E.functions leaf.typed
  case external =>
    intro root X decls input original
    exact fun leaf => CorrectExpr input original E.locals E.functions leaf.typed

def writeCorrect {X F n} (scope : Scope X) (E : Env F n)
    (leaf : WriteLeaf (scope.writes E)) : Prop := by
  revert leaf
  apply Scope.casesOn (motive := fun X scope => WriteLeaf (scope.writes E) → Prop) scope
  case closed => exact fun leaf =>
    ScopedAssignments.TargetCorrect (decls := []) .root E.locals leaf.typed
  case external =>
    intro root X decls input original
    exact fun leaf => ScopedAssignments.TargetCorrect (decls := decls) original E.locals leaf.typed

def Leaf.scopedCorrect (leaf : Leaf) : Prop :=
  match leaf with
  | .read scope E reference => readCorrect scope E reference
  | .write scope E reference => writeCorrect scope E reference

theorem expression_scoped {X F n} (scope : Scope X) (E : Env F n) {term count}
    (typed : BlockScope.ExpressionD scope E term count) (path : Path) :
    All (fun _ leaf => readCorrect scope E leaf)
      (reads (expressionInput scope E typed).2 path) := by
  revert typed
  apply Scope.casesOn (motive := fun X scope =>
    (typed : BlockScope.ExpressionD scope E term count) →
      All (fun _ leaf => readCorrect scope E leaf)
        (reads (expressionInput scope E typed).2 path)) scope
  case closed =>
    intro typed
    refine (all_reads typed path (fun _ leaf => CorrectExpr emptyNames .root E.locals E.functions leaf.typed)).mpr ?_
    exact scoped_reads emptyNames .root E.locals E.functions typed path
      (ScopedExpressions.correctExpr_noMembers emptyNames .root E.locals E.functions
        (by intro ty impossible; cases impossible) typed)
  case external =>
    intro root X decls input original typed
    refine (all_reads typed.val.typed path (fun _ leaf => CorrectExpr input original E.locals E.functions leaf.typed)).mpr ?_
    exact scoped_reads input original E.locals E.functions typed.val.typed path typed.val.correct

theorem assignment_scoped {X F n} (scope : Scope X) (E : Env F n) {paths rhs}
    (typed : BlockScope.AssignmentD scope E paths rhs) (path : Path) :
    All (fun _ leaf => readCorrect scope E leaf)
      (reads (assignmentReads scope E typed) path) := by
  revert typed
  apply Scope.casesOn (motive := fun X scope =>
    (typed : BlockScope.AssignmentD scope E paths rhs) →
      All (fun _ leaf => readCorrect scope E leaf)
        (reads (assignmentReads scope E typed) path)) scope
  case closed =>
    intro typed
    refine (all_reads (ScopedAssignments.rhsD typed) path (fun _ leaf => CorrectExpr emptyNames .root E.locals E.functions leaf.typed)).mpr ?_
    exact scoped_reads emptyNames .root E.locals E.functions (ScopedAssignments.rhsD typed) path
      (ScopedExpressions.correctExpr_noMembers emptyNames .root E.locals E.functions
        (by intro ty impossible; cases impossible) (ScopedAssignments.rhsD typed))
  case external =>
    intro root X decls input original typed
    refine (all_reads (ScopedAssignments.rhsD typed.typed) path (fun _ leaf => CorrectExpr input original E.locals E.functions leaf.typed)).mpr ?_
    exact scoped_reads input original E.locals E.functions
      (ScopedAssignments.rhsD typed.typed) path typed.correct

theorem write_correct {X F n} (scope : Scope X) (E : Env F n)
    (leaf : WriteLeaf (scope.writes E)) : writeCorrect scope E leaf := by
  revert leaf
  apply Scope.casesOn (motive := fun X scope => (leaf : WriteLeaf (scope.writes E)) →
    writeCorrect scope E leaf) scope
  case closed => intro leaf; exact ScopedAssignments.target_scoped .root E.locals leaf.typed
  case external =>
    intro root X decls input original leaf
    exact ScopedAssignments.target_scoped original E.locals leaf.typed

theorem site_scoped (site : TypingSites.Site) :
    AllLeaves (fun _ leaf => leaf.scopedCorrect) (siteTrace site) := by
  cases site with
  | expression scope E tree arity typed =>
      exact (all_mapped (fun _ leaf => leaf.scopedCorrect) .read (Leaf.read scope E)
        (reads (expressionInput scope E typed).2 [])).mpr (expression_scoped scope E typed [])
  | assignment scope E paths rhs typed =>
      change AllLeaves (fun _ leaf => leaf.scopedCorrect) (_++_)
      rw [allLeaves_append]
      constructor
      · apply (all_mapped (fun _ leaf => leaf.scopedCorrect) .read (Leaf.read scope E) _).mpr
        exact assignment_scoped scope E typed []
      · apply (all_mapped (fun _ leaf => leaf.scopedCorrect) .write (Leaf.write scope E) _).mpr
        intro entry present
        exact write_correct scope E entry.2

theorem contextual_scoped (trace : TypingSites.Trace) :
    AllContexts (fun _ leaf => leaf.scopedCorrect) (contextual trace) := by
  refine (all_contextual trace (fun _ leaf => leaf.scopedCorrect)).mpr ?_
  intro entry present
  exact (all_site entry.2 (fun _ leaf => leaf.scopedCorrect)).mp (site_scoped entry.2)

end Solidity.Yul.TypingLeaves
