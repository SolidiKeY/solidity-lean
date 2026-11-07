import Solidity.Yul.Views.RetainedGuardObserver

/-! Finite-horizon observation of actual Source while execution. Guard and body
observer families are explicit exact-projection/retention contracts. Recursion
uses the owner's decreasing horizon; normal restoration, continue, break,
return, guard failure and timeout keep their actual Source behavior. -/
namespace Solidity.Yul.Views

def observeWhile {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : ∀ i, GuardObserver G F i condition) (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  match n with
  | 0 => ((.error .timeout,s),prior)
  | n+1 =>
    let guard := (guards n).observe prior l s
    match guard.1.1 with
    | .error error => ((.error error,guard.1.2),guard.2)
    | .ok (.val (.bool false),l1) => ((.ok (.normal l1),guard.1.2),guard.2)
    | .ok (.val (.bool true),l1) =>
      let step := (bodies n).observe guard.2 l1 guard.1.2
      match step.1.1 with
      | .error error => ((.error error,step.1.2),step.2)
      | .ok (.normal l2) =>
        match l2.restore Γ with
        | .error error => ((.error error,step.1.2),step.2)
        | .ok restored => observeWhile G F n nps ph condition body guards bodies step.2 restored step.1.2 (lp:=lp)
      | .ok (.cont l2) => observeWhile G F n nps ph condition body guards bodies step.2 l2 step.1.2 (lp:=lp)
      | .ok (.brk l2) => ((.ok (.normal l2),step.1.2),step.2)
      | .ok (.ret l2) => ((.ok (.ret l2),step.1.2),step.2)
termination_by structural n

theorem observeWhile_source {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : ∀ i, GuardObserver G F i condition) (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeWhile G F n nps ph condition body guards bodies prior l s (lp:=lp)).1=
      (Source.execS G F n nps ph (.whileLoop (l:=lp) condition body) l).run s := by
  induction n generalizing prior l s with
  | zero => rfl
  | succ n ih =>
    unfold observeWhile
    dsimp only
    rw [Source.execS,Source.Hoare.run_bind,← (guards n).source]
    cases guard : ((guards n).observe prior l s).1 with
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
            · change _ = ((do
                match ← Source.execS G F n nps ph body l1 with
                | .normal l2 => Source.execS G F n nps ph (.whileLoop (l:=lp) condition body) (← Source.EM.lift (l2.restore Γ))
                | .cont l2 => Source.execS G F n nps ph (.whileLoop (l:=lp) condition body) l2
                | .brk l2 => pure (.normal l2)
                | .ret l2 => pure (.ret l2)) : Source.EM E [] (Source.Out E.layout Γ Γ)).run after
              dsimp only
              rw [Source.Hoare.run_bind,← (bodies n).source]
              cases step : ((bodies n).observe ((guards n).observe prior l s).2 l1 after).1 with
              | mk result finalState =>
                cases result with
                | error error => rfl
                | ok out =>
                  cases out with
                  | normal l2 =>
                    dsimp only
                    rw [Source.Hoare.run_bind]
                    cases restoration : l2.restore Γ with
                    | error error => rfl
                    | ok restored => exact ih _ restored finalState
                  | cont l2 => exact ih _ l2 finalState
                  | brk l2 => rfl
                  | ret l2 => rfl

theorem observeWhile_prior {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : ∀ i, GuardObserver G F i condition) (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈prior) :
    scope∈(observeWhile G F n nps ph condition body guards bodies prior l s (lp:=lp)).2 := by
  induction n generalizing prior l s with
  | zero => exact member
  | succ n ih =>
    have guarded := (guards n).prior prior l s scope member
    unfold observeWhile
    dsimp only
    cases guard : ((guards n).observe prior l s).1 with
    | mk result after =>
      cases result with
      | error error => exact guarded
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
            · exact guarded
            · dsimp only
              have kept := (bodies n).prior ((guards n).observe prior l s).2 l1 after scope guarded
              cases step : ((bodies n).observe ((guards n).observe prior l s).2 l1 after).1 with
              | mk result finalState =>
                cases result with
                | error error => exact kept
                | ok out =>
                  cases out with
                  | normal l2 =>
                    dsimp only
                    cases restoration : l2.restore Γ with
                    | error error => exact kept
                    | ok restored => exact ih _ restored finalState kept
                  | cont l2 => exact ih _ l2 finalState kept
                  | brk l2 => exact kept
                  | ret l2 => exact kept

/-- No Source statement runs at horizon zero, so there are no new producers. -/
def zeroStatementObserver {E Γ Γ' R M k} (G : Source.Glob E) (F : Source.Fr)
    (nps : Nat) (ph : Option (Source.Ph E)) (stmt : Source.RStmt E R M k Γ Γ') :
    StatementObserver G F 0 nps ph stmt where
  observe := fun prior _ s => ((.error .timeout,s),prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

/-- Every observed body scope survives restoration, recursive normal/continue
iterations, error, break and return. The guard success is an actual run. -/
theorem observeWhile_body_scopes {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : ∀ i, GuardObserver G F i condition) (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (guard : ((guards n).observe prior l s).1=(.ok (.val (.bool true),l1),after)) (scope)
    (member : scope∈((bodies n).observe ((guards n).observe prior l s).2 l1 after).2) :
    scope∈(observeWhile G F (n+1) nps ph condition body guards bodies prior l s (lp:=lp)).2 := by
  unfold observeWhile
  simp only [guard]
  cases step : ((bodies n).observe ((guards n).observe prior l s).2 l1 after).1 with
  | mk result finalState =>
    cases result with
    | error error => exact member
    | ok out =>
      cases out with
      | normal l2 =>
        dsimp only
        cases restoration : l2.restore Γ with
        | error error => exact member
        | ok restored => exact observeWhile_prior G F n nps ph condition body guards bodies _ restored finalState scope member
      | cont l2 => exact observeWhile_prior G F n nps ph condition body guards bodies _ l2 finalState scope member
      | brk l2 => exact member
      | ret l2 => exact member

/-- Exact finite-horizon loop contract, with both producer families explicit. -/
def whileStatementObserver {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : ∀ i, GuardObserver G F i condition) (bodies : ∀ i, StatementObserver G F i nps ph body) :
    StatementObserver G F n nps ph (.whileLoop (l:=lp) condition body) where
  observe := observeWhile G F n nps ph condition body guards bodies (lp:=lp)
  source := observeWhile_source G F n nps ph condition body guards bodies (lp:=lp)
  prior := observeWhile_prior G F n nps ph condition body guards bodies (lp:=lp)

end Solidity.Yul.Views
