import Solidity.Yul.Views.RetainedForPostIteration

/-! First-test and first-body inventory retention for actual present-post
iterations. Producer families and reached-body evidence stay explicit. These
laws preserve captures through all subsequent outcomes, without claiming
capture completeness, exclusive provenance, or compiler adequacy. -/
namespace Solidity.Yul.Views

/-- Captures in the actual first body survive all later outcomes, including
restoration failure, post failure, backedge timeout, break and return. -/
theorem observeForPostIteration_body_scopes {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (test : ((tests n).observe prior l s).1=(.ok (true,l1),after)) (scope)
    (member : scope∈((bodies n).observe ((tests n).observe prior l s).2 l1 after).2) :
    scope∈(observeForPostIteration G F (n+1) nps ph condition post body tests bodies posts prior l s).2 := by
  unfold observeForPostIteration
  simp only [test]
  cases step : ((bodies n).observe ((tests n).observe prior l s).2 l1 after).1 with
  | mk result finalState =>
    cases result with
    | error error => exact member
    | ok out =>
      cases out with
      | normal l2 =>
        dsimp only
        cases restoration : l2.restore Γ with
        | error error => exact member
        | ok restored =>
          exact observePostThen_post_scopes G F n post (posts n) _
            (observeForPostIteration_prior G F n nps ph condition post body tests bodies posts)
            _ restored finalState scope ((posts n).prior _ restored finalState scope member)
      | cont l2 =>
        exact observePostThen_post_scopes G F n post (posts n) _
          (observeForPostIteration_prior G F n nps ph condition post body tests bodies posts)
          _ l2 finalState scope ((posts n).prior _ l2 finalState scope member)
      | brk l2 => exact member
      | ret l2 => exact member

/-- Actual test captures survive whether the test fails, is false, or enters
the body and post. -/
theorem observeForPostIteration_test_scopes {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈((tests n).observe prior l s).2) :
    scope∈(observeForPostIteration G F (n+1) nps ph condition post body tests bodies posts prior l s).2 := by
  cases test : ((tests n).observe prior l s).1 with
  | mk result after =>
    cases result with
    | error error => simpa only [observeForPostIteration,test] using member
    | ok pair =>
      rcases pair with ⟨go,l1⟩
      cases go
      · simpa only [observeForPostIteration,test] using member
      · exact observeForPostIteration_body_scopes G F n nps ph condition post body tests bodies posts
          prior l l1 s after test scope ((bodies n).prior _ l1 after scope member)


/-- A failing test returns its exact error, state and inventory; neither the
body nor the post is reached. -/
theorem observeForPostIteration_test_error {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (error : Source.Halt)
    (test : ((tests n).observe prior l s).1=(.error error,after)) :
    observeForPostIteration G F (n+1) nps ph condition post body tests bodies posts prior l s=
      ((.error error,after),((tests n).observe prior l s).2) := by
  simp only [observeForPostIteration,test]

end Solidity.Yul.Views
