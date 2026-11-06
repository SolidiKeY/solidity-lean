import Solidity.Yul.Views.RetainedForOptionalTest

/-! Actual initialized for loops transport reached test/body inventories through
loop-scope restoration. All producer families and initializer/test reachability
equations stay explicit; capture completeness and adequacy remain separate. -/
namespace Solidity.Yul.Views

/-- Actual first-test captures survive initialization/iteration composition
and final restoration, including failures. -/
theorem optionalForLoop_test_scopes {E Γ Γ₁ Γ₂ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F (n+1) nps ph init)
    (guards : OptionalForGuards G F condition) (posts : OptionalForPosts G F post)
    (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (l1 : Source.Locals E.layout Γ₁)
    (s after : Source.EMState E []) (initialized : (initializer.observe prior l s).1=(.ok (.normal l1),after))
    (scope) (member : scope∈((optionalForTestObserver G F n condition guards).observe
      (initializer.observe prior l s).2 l1 after).2) :
    scope∈((optionalForLoopStatementObserver G F (n+1) nps ph init condition post body initializer guards posts bodies
      (lp:=lp)).observe prior l s).2 := by
  change scope∈(observeForLoop G F (n+1) nps ph init condition post body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition post body guards posts bodies) prior l s).2
  rw [observeForLoop_iteration_scopes G F (n+1) nps ph init condition post body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition post body guards posts bodies)
    prior l l1 s after initialized]
  exact optionalForIteration_test_scopes G F n nps ph condition post body guards posts bodies
    (initializer.observe prior l s).2 l1 after scope member

/-- Actual first-body captures survive final loop restoration. The body
is reached only after normal initialization and an actual true test. -/
theorem optionalForLoop_body_scopes {E Γ Γ₁ Γ₂ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F (n+1) nps ph init)
    (guards : OptionalForGuards G F condition) (posts : OptionalForPosts G F post)
    (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (l1 l2 : Source.Locals E.layout Γ₁)
    (s after tested : Source.EMState E [])
    (initialized : (initializer.observe prior l s).1=(.ok (.normal l1),after))
    (test : ((optionalForTestObserver G F n condition guards).observe (initializer.observe prior l s).2 l1 after).1=
      (.ok (true,l2),tested)) (scope)
    (member : scope∈((bodies n).observe
      ((optionalForTestObserver G F n condition guards).observe (initializer.observe prior l s).2 l1 after).2
      l2 tested).2) :
    scope∈((optionalForLoopStatementObserver G F (n+1) nps ph init condition post body initializer guards posts bodies
      (lp:=lp)).observe prior l s).2 := by
  change scope∈(observeForLoop G F (n+1) nps ph init condition post body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition post body guards posts bodies) prior l s).2
  rw [observeForLoop_iteration_scopes G F (n+1) nps ph init condition post body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition post body guards posts bodies)
    prior l l1 s after initialized]
  exact optionalForIteration_body_scopes G F n nps ph condition post body guards posts bodies
    (initializer.observe prior l s).2 l1 l2 after tested test scope member

end Solidity.Yul.Views
