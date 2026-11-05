import Solidity.Yul.Views.RetainedForIteration
import Solidity.Yul.Views.RetainedDoWhileObserver

/-! An actual for iteration with absent condition and post reuses body-first
observation through a proved Source equality. The literal test is pure and
reference-free; arbitrary body observers remain explicit. General guard/post
observation and compiler adequacy are not supplied. -/
namespace Solidity.Yul.Views

/-- Observe the actual literal test. It produces no reference or state effect. -/
def literalTrueGuardObserver {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) :
    GuardObserver G F n (.bool true (Γ:=Γ)) where
  observe := fun prior l s =>
    ((Source.EM.sub l (Source.evalE G F n (.bool true)) :
      Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

/-- At every owner horizon, an omitted test/post is exactly body-first looping
with a literal-true test. At horizon one the body times out before any test. -/
theorem forIter_none_none_eq_doWhile {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Source.forIter G F n nps ph .none .none body l).run s=
      (Source.execS G F n nps ph (.doWhile (l:=lp) body (.bool true)) l).run s := by
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change ((do
          match ← Source.execS G F (n+1) nps ph body l with
          | .normal l2 => Source.forIter G F (n+1) nps ph .none .none body (← Source.EM.lift (l2.restore Γ))
          | .cont l2 => Source.forIter G F (n+1) nps ph .none .none body l2
          | .brk l2 => pure (.normal l2)
          | .ret l2 => pure (.ret l2)) : Source.EM E [] (Source.Out E.layout Γ Γ)).run s=
        ((do
          match ← Source.execS G F (n+1) nps ph body l with
          | .normal l2 => Source.execS G F (n+1) nps ph (.doWhile (l:=lp) body (.bool true)) (← Source.EM.lift (l2.restore Γ))
          | .cont l2 => Source.execS G F (n+1) nps ph (.doWhile (l:=lp) body (.bool true)) l2
          | .brk l2 => pure (.normal l2)
          | .ret l2 => pure (.ret l2)) : Source.EM E [] (Source.Out E.layout Γ Γ)).run s
      rw [Source.Hoare.run_bind,Source.Hoare.run_bind]
      cases step : (Source.execS G F (n+1) nps ph body l).run s with
      | mk result after =>
        cases result with
        | error error => rfl
        | ok out =>
          cases out with
          | normal l2 =>
            dsimp only
            rw [Source.Hoare.run_bind,Source.Hoare.run_bind]
            cases restoration : l2.restore Γ with
            | error error => rfl
            | ok restored => exact ih restored after
          | cont l2 => exact ih l2 after
          | brk l2 => rfl
          | ret l2 => rfl

/-- Concrete observer for arbitrary observed bodies with absent test and post.
It reuses the existing body-first observer rather than another evaluator. -/
def unconditionalForIterationObserver {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (bodies : ∀ i, StatementObserver G F i nps ph body) :
    ForIterationObserver G F n nps ph .none .none body where
  observe := observeDoWhile G F n nps ph body (.bool true) (literalTrueGuardObserver G F) bodies (lp:=false)
  source := fun prior l s =>
    (observeDoWhile_source G F n nps ph body (.bool true) (literalTrueGuardObserver G F) bodies prior l s (lp:=false)).trans
      (forIter_none_none_eq_doWhile G F n nps ph body l s (lp:=false)).symm
  prior := observeDoWhile_prior G F n nps ph body (.bool true) (literalTrueGuardObserver G F) bodies (lp:=false)

/-- Captures from the actual first body survive all later for-iteration outcomes. -/
theorem unconditionalForIteration_body_scopes {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (scope)
    (member : scope∈((bodies n).observe prior l s).2) :
    scope∈((unconditionalForIterationObserver G F (n+1) nps ph body bodies).observe prior l s).2 :=
  observeDoWhile_body_scopes G F n nps ph body (.bool true) (literalTrueGuardObserver G F) bodies prior l s scope member (lp:=false)

end Solidity.Yul.Views
