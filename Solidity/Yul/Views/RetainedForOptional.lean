import Solidity.Yul.Views.RetainedForGuarded
import Solidity.Yul.Views.RetainedForUnconditional
import Solidity.Yul.Views.RetainedForPostIteration
import Solidity.Yul.Views.RetainedForComposition

/-! Select existing exact iteration observers for all optional test/post shapes.
Absent expressions require no expression producer and introduce no synthetic
expression. Present-expression and body families stay explicit. This reuses
ForIterationObserver and StatementObserver; no completeness or adequacy follows. -/
namespace Solidity.Yul.Views

/-- Dispatch on actual Source syntax, preserving every component's horizon. -/
def optionalForIterationObserver {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ)
    (post : Source.ROptExpr E Γ) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : match condition with | .none => PUnit | .some ce => ∀ i, GuardObserver G F i ce)
    (posts : match post with | .none => PUnit | .some pe => ∀ i, PostExpressionObserver G F i pe)
    (bodies : ∀ i, StatementObserver G F i nps ph body) :
    ForIterationObserver G F n nps ph condition post body :=
  match condition, post, guards, posts with
  | .none, .none, _, _ => unconditionalForIterationObserver G F n nps ph body bodies
  | .some ce, .none, guards, _ => guardedForIterationObserver G F n nps ph ce body guards bodies
  | .none, .some pe, _, posts => postForIterationObserver G F n nps ph .none pe body
      (absentForTestObserver G F) bodies posts
  | .some ce, .some pe, guards, posts => postForIterationObserver G F n nps ph (.some ce) pe body
      (fun i => presentForTestObserver G F i ce (guards i)) bodies posts

/-- Actual initialization uses the same selected iteration at horizon n,
inside the actual for statement at n+1. -/
def optionalForLoopStatementObserver {E Γ Γ₁ Γ₂ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F n nps ph init)
    (guards : match condition with | .none => PUnit | .some ce => ∀ i, GuardObserver G F i ce)
    (posts : match post with | .none => PUnit | .some pe => ∀ i, PostExpressionObserver G F i pe)
    (bodies : ∀ i, StatementObserver G F i nps ph body) :
    StatementObserver G F (n+1) nps ph (.forLoop (l:=lp) init condition post body) :=
  forLoopStatementObserver G F n nps ph init condition post body initializer
    (optionalForIterationObserver G F n nps ph condition post body guards posts bodies) (lp:=lp)

end Solidity.Yul.Views
