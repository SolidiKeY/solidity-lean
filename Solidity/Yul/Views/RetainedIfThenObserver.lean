import Solidity.Yul.Views.RetainedBranchObserver

/-! One-arm Source conditionals observe the body only on a true guard. The
false branch preserves actual guard locals/state without running a synthetic
statement. Guard-expression intermediates remain uninstrumented. -/
namespace Solidity.Yul.Views

def observeIfThen {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (observer : StatementObserver G F n nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let guard := (Source.EM.sub l (Source.evalE G F n condition) :
    Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s
  match guard.1 with
  | .error error => ((.error error,guard.2),prior)
  | .ok (.val (.bool true),l1) => closeStatementRun (observer.observe prior l1 guard.2)
  | .ok (.val (.bool false),l1) => ((.ok (.normal l1),guard.2),prior)

theorem observeIfThen_source {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (observer : StatementObserver G F n nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeIfThen G F n nps ph condition body observer prior l s).1=
      (Source.execS G F (n+1) nps ph (.ifThen condition body) l).run s := by
  unfold observeIfThen
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
          · rfl
          · change (closeStatementRun (observer.observe prior l1 after)).1=
              ((do let out ← Source.execS G F n nps ph body l1; Source.EM.lift out.close) :
                Source.EM E [] (Source.Out E.layout Γ Γ)).run after
            unfold closeStatementRun
            dsimp only
            rw [Source.Hoare.run_bind, ← observer.source]
            cases arm : (observer.observe prior l1 after).1 with
            | mk result finalState => cases result <;> rfl

theorem observeIfThen_prior {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (observer : StatementObserver G F n nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈prior) :
    scope∈(observeIfThen G F n nps ph condition body observer prior l s).2 := by
  unfold observeIfThen
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
          · exact member
          · exact observer.prior prior l1 after scope member

/-- A false actual guard bypasses the observer and contributes no captures. -/
theorem observeIfThen_false {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (observer : StatementObserver G F n nps ph body)
    (prior : List (EntryReferenceScope E)) (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E []) 
    (guard : (Source.EM.sub l (Source.evalE G F n condition) :
      Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s=
        (.ok (.val (.bool false),l1),after)) :
    observeIfThen G F n nps ph condition body observer prior l s=((.ok (.normal l1),after),prior) := by
  simp only [observeIfThen,guard]

/-- True uses exactly the supplied observer after actual guard effects. -/
theorem observeIfThen_true {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (observer : StatementObserver G F n nps ph body)
    (prior : List (EntryReferenceScope E)) (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (guard : (Source.EM.sub l (Source.evalE G F n condition) :
      Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s=
        (.ok (.val (.bool true),l1),after)) :
    observeIfThen G F n nps ph condition body observer prior l s=closeStatementRun (observer.observe prior l1 after) := by
  simp only [observeIfThen,guard]

/-- The arm remains an explicit exact Source observer contract. -/
def ifThenStatementObserver {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (observer : StatementObserver G F n nps ph body) :
    StatementObserver G F (n+1) nps ph (.ifThen condition body) where
  observe := observeIfThen G F n nps ph condition body observer
  source := observeIfThen_source G F n nps ph condition body observer
  prior := observeIfThen_prior G F n nps ph condition body observer

end Solidity.Yul.Views
