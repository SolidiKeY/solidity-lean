import Solidity.Yul.Views.RetainedForIteration
import Solidity.Yul.Views.RetainedWhileObserver

/-! Actual for iterations with a present guard and absent post reuse observed
while execution through an exact Source equality. Guard/body observer families
stay explicit; no post-expression producer or compiler adequacy is supplied. -/
namespace Solidity.Yul.Views

theorem forIter_some_none_eq_while {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Source.forIter G F n nps ph (.some condition) .none body l).run s=
      (Source.execS G F n nps ph (.whileLoop (l:=lp) condition body) l).run s := by
  have pure_run {α : Type} (a : α) (state : Source.EMState E []) :
      (pure a : Source.EM E [] α).run state=(.ok a,state) := rfl
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    rw [Source.forIter,Source.execS]
    simp only [Source.Hoare.run_bind]
    cases guard : (Source.EM.sub l (Source.evalE G F n condition) :
        Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s with
    | mk result after =>
      cases result with
      | error error => rfl
      | ok pair =>
        rcases pair with ⟨value,l1⟩
        cases value with
        | val value =>
          cases value with
          | memRef h _ => cases h
          | storRef h _ => cases h
          | cdRef h _ _ => cases h
          | bool flag =>
            cases flag
            · rfl
            · simp only [show (Source.getV (.val (.bool true)) : Source.EM E [] (Source.Val E.layout .bool)).run after=
                  (.ok (.bool true),after) from rfl]
              simp only [Bool.not_true,Bool.false_eq_true,if_false,Source.Hoare.run_bind,pure_run]
              cases step : (Source.execS G F n nps ph body l1).run after with
              | mk result finalState =>
                cases result with
                | error error => rfl
                | ok out =>
                  cases out with
                  | normal l2 =>
                    dsimp only
                    cases restoration : l2.restore Γ with
                    | error error => rfl
                    | ok restored => exact ih restored finalState
                  | cont l2 => exact ih l2 finalState
                  | brk l2 => rfl
                  | ret l2 => rfl

/-- Concrete producer at every actual horizon, reusing the proved while observer. -/
def guardedForIterationObserver {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) :
    ForIterationObserver G F n nps ph (.some condition) .none body where
  observe := observeWhile G F n nps ph condition body guards bodies (lp:=false)
  source := fun prior l s =>
    (observeWhile_source G F n nps ph condition body guards bodies prior l s (lp:=false)).trans
      (forIter_some_none_eq_while G F n nps ph condition body l s (lp:=false)).symm
  prior := observeWhile_prior G F n nps ph condition body guards bodies (lp:=false)

/-- Captures inside a failing actual guard survive before the body is reached. -/
theorem guardedForIteration_guard_error {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s after : Source.EMState E []) (error)
    (run : ((guards n).observe prior l s).1=(.error error,after)) :
    (guardedForIterationObserver G F (n+1) nps ph condition body guards bodies).observe prior l s=
      ((.error error,after),((guards n).observe prior l s).2) := by
  simp only [guardedForIterationObserver,observeWhile,run]

/-- A false actual guard skips the body and returns precisely its own inventory. -/
theorem guardedForIteration_guard_false {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (run : ((guards n).observe prior l s).1=(.ok (.val (.bool false),l1),after)) :
    (guardedForIterationObserver G F (n+1) nps ph condition body guards bodies).observe prior l s=
      ((.ok (.normal l1),after),((guards n).observe prior l s).2) := by
  simp only [guardedForIterationObserver,observeWhile,run]

/-- Actual first-body captures survive every subsequent iteration outcome. -/
theorem guardedForIteration_body_scopes {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (run : ((guards n).observe prior l s).1=(.ok (.val (.bool true),l1),after)) (scope)
    (member : scope∈((bodies n).observe ((guards n).observe prior l s).2 l1 after).2) :
    scope∈((guardedForIterationObserver G F (n+1) nps ph condition body guards bodies).observe prior l s).2 :=
  observeWhile_body_scopes G F n nps ph condition body guards bodies prior l l1 s after run scope member (lp:=false)

end Solidity.Yul.Views
