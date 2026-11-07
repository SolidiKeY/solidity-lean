import Solidity.Yul.Views.RetainedForOptionalBody

/-! Actual first-test inventory retention across all optional for-loop shapes.
The no-post guarded route uses the existing while execution; present posts
use their established iteration law. No capture completeness is assumed. -/
namespace Solidity.Yul.Views

/-- Actual guard captures survive false exit, failure, and all later body or
recursive outcomes. The producer families remain explicit. -/
theorem observeWhile_guard_scopes {E Γ Γ₁ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : ∀ i, GuardObserver G F i condition) (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈((guards n).observe prior l s).2) :
    scope∈(observeWhile G F (n+1) nps ph condition body guards bodies prior l s (lp:=lp)).2 := by
  cases actual : ((guards n).observe prior l s).1 with
  | mk result after =>
    cases result with
    | error error => simpa only [observeWhile,actual] using member
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
          · simpa only [observeWhile,actual] using member
          · exact observeWhile_body_scopes G F n nps ph condition body guards bodies
              prior l l1 s after actual scope ((bodies n).prior _ l1 after scope member) (lp:=lp)

/-- The selected actual optional test's captures survive every iteration
outcome, without requiring the test to succeed or return true. -/
theorem optionalForIteration_test_scopes {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ)
    (post : Source.ROptExpr E Γ) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : OptionalForGuards G F condition) (posts : OptionalForPosts G F post)
    (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈((optionalForTestObserver G F n condition guards).observe prior l s).2) :
    scope∈((optionalForIterationObserver G F (n+1) nps ph condition post body guards posts bodies).observe prior l s).2 := by
  cases condition with
  | none =>
    exact (optionalForIterationObserver G F (n+1) nps ph .none post body guards posts bodies).prior prior l s scope member
  | some ce =>
    cases post with
    | none => exact observeWhile_guard_scopes G F n nps ph ce body guards bodies prior l s scope member (lp:=false)
    | some pe =>
      exact observeForPostIteration_test_scopes G F n nps ph (.some ce) pe body
        (fun i => presentForTestObserver G F i ce (guards i)) bodies posts prior l s scope member

end Solidity.Yul.Views
