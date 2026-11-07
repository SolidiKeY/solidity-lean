import Solidity.Yul.Views.RetainedForTest
import Solidity.Yul.Views.RetainedForPost

/-! Full finite-horizon for-iteration observation with a present post. The exact
optional test, body and post families remain explicit. Normal restoration and
continue reach the post; break/return bypass it; actual errors/state and the
owner's decreasing horizon are preserved. -/
namespace Solidity.Yul.Views

/-- Factor the owner's optional test from its generated continuation. This
is an equality of actual Source computations, not an extra evaluator. -/
theorem forIter_present_post_step {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Source.forIter G F (n+1) nps ph condition (.some post) body l).run s=
      ((do let (go,l1) ← forTestEvaluation G F n condition l
           if !go then pure (.normal l1) else do
             match ← Source.execS G F n nps ph body l1 with
             | .normal l2 => do
               let restored ← Source.EM.lift (l2.restore Γ)
               let l3 ← (do pure (← Source.EM.sub restored (Source.evalE G F n post)).2)
               Source.forIter G F n nps ph condition (.some post) body l3
             | .cont l2 => do
               let l3 ← (do pure (← Source.EM.sub l2 (Source.evalE G F n post)).2)
               Source.forIter G F n nps ph condition (.some post) body l3
             | .brk l2 => pure (.normal l2)
             | .ret l2 => pure (.ret l2)) : Source.EM E [] (Source.Out E.layout Γ Γ)).run s := by
  unfold forTestEvaluation
  cases condition with
  | none => rw [Source.forIter]; simp only [pure_bind, bind_assoc] <;> rfl
  | some ce =>
    rw [Source.forIter]
    simp only [Source.Hoare.run_bind]
    cases guard : (Source.EM.sub l (Source.evalE G F n ce) :
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
            simp only [show (Source.getV (.val (.bool flag)) : Source.EM E [] (Source.Val E.layout .bool)).run after =
                (.ok (.bool flag),after) from rfl, pure_bind, bind_assoc] <;> rfl

def observeForPostIteration {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  match n with
  | 0 => ((.error .timeout,s),prior)
  | n+1 =>
    let test := (tests n).observe prior l s
    match test.1.1 with
    | .error error => ((.error error,test.1.2),test.2)
    | .ok (false,l1) => ((.ok (.normal l1),test.1.2),test.2)
    | .ok (true,l1) =>
      let step := (bodies n).observe test.2 l1 test.1.2
      let advance := fun l2 => observePostThen G F n post (posts n)
        (fun prior l s => observeForPostIteration G F n nps ph condition post body tests bodies posts prior l s)
        step.2 l2 step.1.2
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

theorem observeForPostIteration_source {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeForPostIteration G F n nps ph condition post body tests bodies posts prior l s).1=
      (Source.forIter G F n nps ph condition (.some post) body l).run s := by
  induction n generalizing prior l s with
  | zero => rfl
  | succ n ih =>
    unfold observeForPostIteration
    dsimp only
    rw [forIter_present_post_step,Source.Hoare.run_bind]
    dsimp only
    have test_source := (tests n).source prior l s
    rw [← test_source]
    cases test : ((tests n).observe prior l s).1 with
    | mk result after =>
      cases result with
      | error error => rfl
      | ok pair =>
        rcases pair with ⟨go,l1⟩
        cases go
        · rfl
        · dsimp only
          simp only [Bool.not_true,Bool.false_eq_true,if_false,Source.Hoare.run_bind]
          rw [← (bodies n).source ((tests n).observe prior l s).2 l1 after]
          cases step : ((bodies n).observe ((tests n).observe prior l s).2 l1 after).1 with
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
                | ok restored =>
                  exact observePostThen_source G F n post (posts n) _
                    (fun l1 => Source.forIter G F n nps ph _ (.some post) body l1) ih _ restored finalState
              | cont l2 =>
                exact observePostThen_source G F n post (posts n) _
                  (fun l1 => Source.forIter G F n nps ph _ (.some post) body l1) ih _ l2 finalState
              | brk l2 => rfl
              | ret l2 => rfl

theorem observeForPostIteration_prior {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈prior) :
    scope∈(observeForPostIteration G F n nps ph condition post body tests bodies posts prior l s).2 := by
  induction n generalizing prior l s scope with
  | zero => exact member
  | succ n ih =>
    have tested := (tests n).prior prior l s scope member
    unfold observeForPostIteration
    dsimp only
    cases test : ((tests n).observe prior l s).1 with
    | mk result after =>
      cases result with
      | error error => exact tested
      | ok pair =>
        rcases pair with ⟨go,l1⟩
        cases go
        · exact tested
        · dsimp only
          have kept := (bodies n).prior ((tests n).observe prior l s).2 l1 after scope tested
          cases step : ((bodies n).observe ((tests n).observe prior l s).2 l1 after).1 with
          | mk result finalState =>
            cases result with
            | error error => exact kept
            | ok out =>
              cases out with
              | normal l2 =>
                dsimp only
                cases restoration : l2.restore Γ with
                | error error => exact kept
                | ok restored =>
                  exact observePostThen_post_scopes G F n post (posts n) _ ih _ restored finalState scope
                    ((posts n).prior _ restored finalState scope kept)
              | cont l2 =>
                exact observePostThen_post_scopes G F n post (posts n) _ ih _ l2 finalState scope
                  ((posts n).prior _ l2 finalState scope kept)
              | brk l2 => exact kept
              | ret l2 => exact kept

/-- All horizons, with exact test/body/post observer families as premises. -/
def postForIterationObserver {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post) :
    ForIterationObserver G F n nps ph condition (.some post) body where
  observe := observeForPostIteration G F n nps ph condition post body tests bodies posts
  source := observeForPostIteration_source G F n nps ph condition post body tests bodies posts
  prior := observeForPostIteration_prior G F n nps ph condition post body tests bodies posts

/-- A reached normal-body post retains captures through every later outcome. -/
theorem observeForPostIteration_normal_post_scopes {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l l1 restored : Source.Locals E.layout Γ)
    (l2 : Source.Locals E.layout Γ₁) (s after finalState : Source.EMState E [])
    (test : ((tests n).observe prior l s).1=(.ok (true,l1),after))
    (step : ((bodies n).observe ((tests n).observe prior l s).2 l1 after).1=(.ok (.normal l2),finalState))
    (restoration : l2.restore Γ=.ok restored) (scope)
    (member : scope∈((posts n).observe
      ((bodies n).observe ((tests n).observe prior l s).2 l1 after).2 restored finalState).2) :
    scope∈(observeForPostIteration G F (n+1) nps ph condition post body tests bodies posts prior l s).2 := by
  simp only [observeForPostIteration,test,step,restoration]
  exact observePostThen_post_scopes G F n post (posts n) _
    (observeForPostIteration_prior G F n nps ph condition post body tests bodies posts)
    _ restored finalState scope member

/-- A reached continue-body post retains captures through every later outcome. -/
theorem observeForPostIteration_continue_post_scopes {E Γ Γ₁ R M σ} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ) (post : Source.RExpr E Γ σ)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) (tests : ∀ i, ForTestObserver G F i condition)
    (bodies : ∀ i, StatementObserver G F i nps ph body) (posts : ∀ i, PostExpressionObserver G F i post)
    (prior : List (EntryReferenceScope E)) (l l1 l2 : Source.Locals E.layout Γ) (s after finalState : Source.EMState E [])
    (test : ((tests n).observe prior l s).1=(.ok (true,l1),after))
    (step : ((bodies n).observe ((tests n).observe prior l s).2 l1 after).1=(.ok (.cont l2),finalState))
    (scope)
    (member : scope∈((posts n).observe
      ((bodies n).observe ((tests n).observe prior l s).2 l1 after).2 l2 finalState).2) :
    scope∈(observeForPostIteration G F (n+1) nps ph condition post body tests bodies posts prior l s).2 := by
  simp only [observeForPostIteration,test,step]
  exact observePostThen_post_scopes G F n post (posts n) _
    (observeForPostIteration_prior G F n nps ph condition post body tests bodies posts)
    _ l2 finalState scope member

end Solidity.Yul.Views
