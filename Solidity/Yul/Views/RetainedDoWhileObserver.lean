import Solidity.Yul.Views.RetainedLoopTest
import Solidity.Yul.Views.RetainedWhileObserver

/-! Actual finite-horizon body-first loop observation. Normal body completion
restores locals before the test; continue reaches the test directly, while
break and return bypass it. All observer-family obligations remain explicit. -/
namespace Solidity.Yul.Views

def observeDoWhile {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.RExpr E Γ .bool) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  match n with
  | 0 => ((.error .timeout,s),prior)
  | n+1 =>
    let step := (bodies n).observe prior l s
    let advance := fun l1 => observeLoopTest G F n condition (guards n)
      (fun prior l s => observeDoWhile G F n nps ph body condition guards bodies prior l s (lp:=lp)) step.2 l1 step.1.2
    match step.1.1 with
    | .error error => ((.error error,step.1.2),step.2)
    | .ok (.normal l2) =>
      match l2.restore Γ with
      | .error error => ((.error error,step.1.2),step.2)
      | .ok restored => advance restored
    | .ok (.cont l2) => advance l2
    | .ok (.brk l2) => ((.ok (.normal l2),step.1.2),step.2)
    | .ok (.ret l2) => ((.ok (.ret l2),step.1.2),step.2)
termination_by structural n

theorem observeDoWhile_source {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.RExpr E Γ .bool) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeDoWhile G F n nps ph body condition guards bodies prior l s (lp:=lp)).1=
      (Source.execS G F n nps ph (.doWhile (l:=lp) body condition) l).run s := by
  induction n generalizing prior l s with
  | zero => rfl
  | succ n ih =>
    unfold observeDoWhile
    dsimp only
    rw [Source.execS,Source.Hoare.run_bind,← (bodies n).source]
    cases step : ((bodies n).observe prior l s).1 with
    | mk result after =>
      cases result with
      | error error => rfl
      | ok out =>
        cases out with
        | normal l2 =>
          dsimp only
          rw [Source.Hoare.run_bind]
          cases restoration : l2.restore Γ with
          | error error => rfl
          | ok restored =>
            exact observeLoopTest_source G F n condition (guards n) _
              (fun l1 => Source.execS G F n nps ph (.doWhile (l:=lp) body condition) l1) ih _ restored after
        | cont l2 =>
          exact observeLoopTest_source G F n condition (guards n) _
            (fun l1 => Source.execS G F n nps ph (.doWhile (l:=lp) body condition) l1) ih _ l2 after
        | brk l2 => rfl
        | ret l2 => rfl

theorem observeDoWhile_prior {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.RExpr E Γ .bool) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (scope) (member : scope∈prior) :
    scope∈(observeDoWhile G F n nps ph body condition guards bodies prior l s (lp:=lp)).2 := by
  induction n generalizing prior l s scope with
  | zero => exact member
  | succ n ih =>
    have kept := (bodies n).prior prior l s scope member
    unfold observeDoWhile
    dsimp only
    cases step : ((bodies n).observe prior l s).1 with
    | mk result after =>
      cases result with
      | error error => exact kept
      | ok out =>
        cases out with
        | normal l2 =>
          dsimp only
          cases restoration : l2.restore Γ with
          | error error => exact kept
          | ok restored =>
            exact observeLoopTest_guard_scopes G F n condition (guards n) _ ih _ restored after scope
              ((guards n).prior _ restored after scope kept)
        | cont l2 =>
          exact observeLoopTest_guard_scopes G F n condition (guards n) _ ih _ l2 after scope
            ((guards n).prior _ l2 after scope kept)
        | brk l2 => exact kept
        | ret l2 => exact kept

/-- First-body captures survive the subsequent test and all later iterations. -/
theorem observeDoWhile_body_scopes {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.RExpr E Γ .bool) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (scope)
    (member : scope∈((bodies n).observe prior l s).2) :
    scope∈(observeDoWhile G F (n+1) nps ph body condition guards bodies prior l s (lp:=lp)).2 := by
  unfold observeDoWhile
  dsimp only
  cases step : ((bodies n).observe prior l s).1 with
  | mk result after =>
    cases result with
    | error error => exact member
    | ok out =>
      cases out with
      | normal l2 =>
        dsimp only
        cases restoration : l2.restore Γ with
        | error error => exact member
        | ok restored =>
          exact observeLoopTest_guard_scopes G F n condition (guards n) _
            (observeDoWhile_prior G F n nps ph body condition guards bodies (lp:=lp)) _ restored after scope
            ((guards n).prior _ restored after scope member)
      | cont l2 =>
        exact observeLoopTest_guard_scopes G F n condition (guards n) _
          (observeDoWhile_prior G F n nps ph body condition guards bodies (lp:=lp)) _ l2 after scope
          ((guards n).prior _ l2 after scope member)
      | brk l2 => exact member
      | ret l2 => exact member

/-- Concrete constructor from explicit exact guard/body observation families. -/
def doWhileStatementObserver {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.RExpr E Γ .bool) (guards : ∀ i, GuardObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) :
    StatementObserver G F n nps ph (.doWhile (l:=lp) body condition) where
  observe := observeDoWhile G F n nps ph body condition guards bodies (lp:=lp)
  source := observeDoWhile_source G F n nps ph body condition guards bodies (lp:=lp)
  prior := observeDoWhile_prior G F n nps ph body condition guards bodies (lp:=lp)

end Solidity.Yul.Views
