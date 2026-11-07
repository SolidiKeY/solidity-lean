import Solidity.Yul.Views.RetainedForLoopScopes

/-! Reached present-post captures survive actual initialization and later loop
outcomes. Normal and continue prefixes remain explicit; no execution of a
bypassed post, capture completeness, or adequacy is inferred. -/
namespace Solidity.Yul.Views

/-- The existing present-post route uses the selected actual test adapter. -/
theorem optionalForIteration_present_post {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (guards : OptionalForGuards G F condition)
    (posts : ∀ i, PostExpressionObserver G F i post) (bodies : ∀ i, StatementObserver G F i nps ph body) :
    optionalForIterationObserver G F n nps ph condition (.some post) body guards posts bodies=
      postForIterationObserver G F n nps ph condition post body
        (fun i => optionalForTestObserver G F i condition guards) bodies posts := by
  cases condition <;> rfl

/-- A reached normal-body post survives all subsequent loop outcomes. -/
theorem optionalForLoop_normal_post_scopes {E Γ Γ₁ Γ₂ R M σ} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.RExpr E Γ₁ σ) (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F (n+1) nps ph init) (guards : OptionalForGuards G F condition)
    (posts : ∀ i, PostExpressionObserver G F i post) (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ)
    (l1 l2 restored : Source.Locals E.layout Γ₁) (l3 : Source.Locals E.layout Γ₂)
    (s after tested stepped : Source.EMState E [])
    (initialized : (initializer.observe prior l s).1=(.ok (.normal l1),after))
    (test : ((optionalForTestObserver G F n condition guards).observe (initializer.observe prior l s).2 l1 after).1=
      (.ok (true,l2),tested))
    (step : ((bodies n).observe ((optionalForTestObserver G F n condition guards).observe
      (initializer.observe prior l s).2 l1 after).2 l2 tested).1=(.ok (.normal l3),stepped))
    (restoration : l3.restore Γ₁=.ok restored) (scope)
    (member : scope∈((posts n).observe ((bodies n).observe
      ((optionalForTestObserver G F n condition guards).observe (initializer.observe prior l s).2 l1 after).2
      l2 tested).2 restored stepped).2) :
    scope∈((optionalForLoopStatementObserver G F (n+1) nps ph init condition (.some post) body initializer guards posts bodies
      (lp:=lp)).observe prior l s).2 := by
  change scope∈(observeForLoop G F (n+1) nps ph init condition (.some post) body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition (.some post) body guards posts bodies) prior l s).2
  rw [observeForLoop_iteration_scopes G F (n+1) nps ph init condition (.some post) body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition (.some post) body guards posts bodies)
    prior l l1 s after initialized]
  rw [optionalForIteration_present_post]
  exact observeForPostIteration_normal_post_scopes G F n nps ph condition post body
    (fun i => optionalForTestObserver G F i condition guards) bodies posts (initializer.observe prior l s).2
    l1 l2 restored l3 after tested stepped test step restoration scope member

/-- A reached continue-body post survives all subsequent loop outcomes. -/
theorem optionalForLoop_continue_post_scopes {E Γ Γ₁ Γ₂ R M σ} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.RExpr E Γ₁ σ) (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F (n+1) nps ph init) (guards : OptionalForGuards G F condition)
    (posts : ∀ i, PostExpressionObserver G F i post) (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ)
    (l1 l2 l3 : Source.Locals E.layout Γ₁)
    (s after tested stepped : Source.EMState E [])
    (initialized : (initializer.observe prior l s).1=(.ok (.normal l1),after))
    (test : ((optionalForTestObserver G F n condition guards).observe (initializer.observe prior l s).2 l1 after).1=
      (.ok (true,l2),tested))
    (step : ((bodies n).observe ((optionalForTestObserver G F n condition guards).observe
      (initializer.observe prior l s).2 l1 after).2 l2 tested).1=(.ok (.cont l3),stepped))
    (scope)
    (member : scope∈((posts n).observe ((bodies n).observe
      ((optionalForTestObserver G F n condition guards).observe (initializer.observe prior l s).2 l1 after).2
      l2 tested).2 l3 stepped).2) :
    scope∈((optionalForLoopStatementObserver G F (n+1) nps ph init condition (.some post) body initializer guards posts bodies
      (lp:=lp)).observe prior l s).2 := by
  change scope∈(observeForLoop G F (n+1) nps ph init condition (.some post) body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition (.some post) body guards posts bodies) prior l s).2
  rw [observeForLoop_iteration_scopes G F (n+1) nps ph init condition (.some post) body initializer
    (optionalForIterationObserver G F (n+1) nps ph condition (.some post) body guards posts bodies)
    prior l l1 s after initialized]
  rw [optionalForIteration_present_post]
  exact observeForPostIteration_continue_post_scopes G F n nps ph condition post body
    (fun i => optionalForTestObserver G F i condition guards) bodies posts (initializer.observe prior l s).2
    l1 l2 l3 after tested stepped test step scope member

end Solidity.Yul.Views
