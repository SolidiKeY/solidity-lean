import Solidity.Yul.Views.RetainedGuardObserver

/-! Observed guards compose with actual two-arm Source conditionals. Captured
guard inventories survive conversion failure and either selected body. The
unselected body is not observed; general capture completeness stays open. -/
namespace Solidity.Yul.Views

def observeGuardedIfElse {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (guardObserver : GuardObserver G F n condition)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let guard := guardObserver.observe prior l s
  match guard.1.1 with
  | .error error => ((.error error,guard.1.2),guard.2)
  | .ok (.val (.bool true),l1) => closeStatementRun (yesObserver.observe guard.2 l1 guard.1.2)
  | .ok (.val (.bool false),l1) => closeStatementRun (noObserver.observe guard.2 l1 guard.1.2)

theorem observeGuardedIfElse_source {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (guardObserver : GuardObserver G F n condition)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeGuardedIfElse G F n nps ph condition yes no guardObserver yesObserver noObserver prior l s).1=
      (Source.execS G F (n+1) nps ph (.ifElse condition yes no) l).run s := by
  unfold observeGuardedIfElse
  dsimp only
  rw [Source.execS, Source.Hoare.run_bind, ← guardObserver.source]
  cases guard : (guardObserver.observe prior l s).1 with
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
          · change (closeStatementRun (noObserver.observe (guardObserver.observe prior l s).2 l1 after)).1=
              ((do let out ← Source.execS G F n nps ph no l1; Source.EM.lift out.close) :
                Source.EM E [] (Source.Out E.layout Γ Γ)).run after
            unfold closeStatementRun
            dsimp only
            rw [Source.Hoare.run_bind, ← noObserver.source]
            cases arm : (noObserver.observe (guardObserver.observe prior l s).2 l1 after).1 with
            | mk result finalState => cases result <;> rfl
          · change (closeStatementRun (yesObserver.observe (guardObserver.observe prior l s).2 l1 after)).1=
              ((do let out ← Source.execS G F n nps ph yes l1; Source.EM.lift out.close) :
                Source.EM E [] (Source.Out E.layout Γ Γ)).run after
            unfold closeStatementRun
            dsimp only
            rw [Source.Hoare.run_bind, ← yesObserver.source]
            cases arm : (yesObserver.observe (guardObserver.observe prior l s).2 l1 after).1 with
            | mk result finalState => cases result <;> rfl

/-- Every captured guard scope survives errors and either observed arm. -/
theorem observeGuardedIfElse_guard_scopes {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (guardObserver : GuardObserver G F n condition)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈(guardObserver.observe prior l s).2) :
    scope∈(observeGuardedIfElse G F n nps ph condition yes no guardObserver yesObserver noObserver prior l s).2 := by
  unfold observeGuardedIfElse
  dsimp only
  cases guard : (guardObserver.observe prior l s).1 with
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
          · exact noObserver.prior _ l1 after scope member
          · exact yesObserver.prior _ l1 after scope member

/-- The actual selected observer receives all guard captures and reached state. -/
theorem observeGuardedIfElse_selected_scopes {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (guardObserver : GuardObserver G F n condition)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E))
    (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E []) (flag : Bool)
    (run : (guardObserver.observe prior l s).1=(.ok (.val (.bool flag),l1),after)) :
    (observeGuardedIfElse G F n nps ph condition yes no guardObserver yesObserver noObserver prior l s).2=
      if flag then (yesObserver.observe (guardObserver.observe prior l s).2 l1 after).2
      else (noObserver.observe (guardObserver.observe prior l s).2 l1 after).2 := by
  cases flag <;> simp only [observeGuardedIfElse,run,closeStatementRun_scopes,Bool.false_eq_true,if_false,if_true]

/-- A failing guard returns its exact error/state and complete captured list. -/
theorem observeGuardedIfElse_error {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (guardObserver : GuardObserver G F n condition)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no)
    (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s after : Source.EMState E []) (error)
    (run : (guardObserver.observe prior l s).1=(.error error,after)) :
    observeGuardedIfElse G F n nps ph condition yes no guardObserver yesObserver noObserver prior l s=
      ((.error error,after),(guardObserver.observe prior l s).2) := by
  simp only [observeGuardedIfElse,run]

/-- Exact observer contract, leaving all guard/body producer fields explicit. -/
def guardedIfElseStatementObserver {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (yes : Source.RStmt E R M k Γ Γ₁) (no : Source.RStmt E R M k Γ Γ₂)
    (guardObserver : GuardObserver G F n condition)
    (yesObserver : StatementObserver G F n nps ph yes) (noObserver : StatementObserver G F n nps ph no) :
    StatementObserver G F (n+1) nps ph (.ifElse condition yes no) where
  observe := observeGuardedIfElse G F n nps ph condition yes no guardObserver yesObserver noObserver
  source := observeGuardedIfElse_source G F n nps ph condition yes no guardObserver yesObserver noObserver
  prior := fun prior l s scope member => observeGuardedIfElse_guard_scopes G F n nps ph condition yes no
    guardObserver yesObserver noObserver prior l s scope (guardObserver.prior prior l s scope member)

end Solidity.Yul.Views
