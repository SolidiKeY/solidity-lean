import Solidity.Yul.Views.RetainedBlockObserver

/-! Source-selected statement observers. The actual guard runs once with its
real state/local effects; only the selected arm is observed. Guard-expression
intermediates remain uninstrumented. Neither contract asserts completeness. -/
namespace Solidity.Yul.Views

/-- Apply actual owner scope closure without removing any retained scopes. -/
def closeStatementRun {E Γ Γ'}
    (observed : (Except Source.Halt (Source.Out E.layout Γ Γ') × Source.EMState E []) × List (EntryReferenceScope E)) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let result := match observed.1.1 with
    | .error error => (.error error,observed.1.2)
    | .ok out => (Source.EM.lift out.close : Source.EM E [] (Source.Out E.layout Γ Γ)).run observed.1.2
  (result,observed.2)

theorem closeStatementRun_scopes {E Γ Γ'}
    (observed : (Except Source.Halt (Source.Out E.layout Γ Γ') × Source.EMState E []) × List (EntryReferenceScope E)) :
    (closeStatementRun observed).2=observed.2 := rfl

/-- Conditional on real observers for both actual arm statements. Only the
selected observer is called, after actual guard evaluation in Source.EM.sub. -/
def observeIfElse {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let guard := (Source.EM.sub l (Source.evalE G F n condition) :
    Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s
  match guard.1 with
  | .error error => ((.error error,guard.2),prior)
  | .ok (.val (.bool true),l1) => closeStatementRun (yesObserver.observe prior l1 guard.2)
  | .ok (.val (.bool false),l1) => closeStatementRun (noObserver.observe prior l1 guard.2)

theorem observeIfElse_source {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeIfElse G F n nps ph condition yes no yesObserver noObserver prior l s).1=
      (Source.execS G F (n+1) nps ph (.ifElse condition yes no) l).run s := by
  unfold observeIfElse
  dsimp only
  rw [Source.execS, Source.Hoare.run_bind]
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
          · change (closeStatementRun (noObserver.observe prior l1 after)).1=
              ((do let out ← Source.execS G F n nps ph no l1; Source.EM.lift out.close) :
                Source.EM E [] (Source.Out E.layout Γ Γ)).run after
            unfold closeStatementRun
            dsimp only
            rw [Source.Hoare.run_bind, ← noObserver.source]
            cases arm : (noObserver.observe prior l1 after).1 with
            | mk result finalState => cases result <;> rfl
          · change (closeStatementRun (yesObserver.observe prior l1 after)).1=
              ((do let out ← Source.execS G F n nps ph yes l1; Source.EM.lift out.close) :
                Source.EM E [] (Source.Out E.layout Γ Γ)).run after
            unfold closeStatementRun
            dsimp only
            rw [Source.Hoare.run_bind, ← yesObserver.source]
            cases arm : (yesObserver.observe prior l1 after).1 with
            | mk result finalState => cases result <;> rfl

theorem observeIfElse_prior {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈prior) :
    scope∈(observeIfElse G F n nps ph condition yes no yesObserver noObserver prior l s).2 := by
  unfold observeIfElse
  dsimp only
  cases guard : (Source.EM.sub l (Source.evalE G F n condition) :
      Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s with
  | mk result after =>
    cases result with
    | error error => exact member
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
          · exact noObserver.prior prior l1 after scope member
          · exact yesObserver.prior prior l1 after scope member

/-- The scope list is exactly the selected observer's list; the unselected
observer contributes nothing. Actual guard locals and state are passed on. -/
theorem observeIfElse_selected_scopes {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E []) (flag : Bool)
    (guard : (Source.EM.sub l (Source.evalE G F n condition) :
      Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s=
        (.ok (.val (.bool flag),l1),after)) :
    (observeIfElse G F n nps ph condition yes no yesObserver noObserver prior l s).2=
      if flag then (yesObserver.observe prior l1 after).2 else (noObserver.observe prior l1 after).2 := by
  cases flag <;> simp only [observeIfElse,guard,closeStatementRun_scopes, Bool.false_eq_true, if_false, if_true]

/-- Guard failure retains its exact Source error/state and the inherited list. -/
theorem observeIfElse_guard_error {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s after : Source.EMState E []) (error)
    (guard : (Source.EM.sub l (Source.evalE G F n condition) :
      Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s=(.error error,after)) :
    observeIfElse G F n nps ph condition yes no yesObserver noObserver prior l s=((.error error,after),prior) := by
  simp only [observeIfElse,guard]

/-- A concrete constructor from the explicit actual arm observer contracts. -/
def ifElseStatementObserver {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no) :
    StatementObserver G F (n+1) nps ph (.ifElse condition yes no) where
  observe := observeIfElse G F n nps ph condition yes no yesObserver noObserver
  source := observeIfElse_source G F n nps ph condition yes no yesObserver noObserver
  prior := observeIfElse_prior G F n nps ph condition yes no yesObserver noObserver

end Solidity.Yul.Views
