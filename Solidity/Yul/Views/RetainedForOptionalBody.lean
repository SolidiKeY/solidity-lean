import Solidity.Yul.Views.RetainedForOptional
import Solidity.Yul.Views.RetainedForPostRetention

/-! Body capture retention across all optional test/post shapes. Entry into
the body requires its actual true-test result; optional dispatch does not
supply capture completeness or source/compiler adequacy. -/
namespace Solidity.Yul.Views

/-- Use the actual absent-test or present-guard adapter at its unchanged horizon. -/
def optionalForTestObserver {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.ROptBool E Γ)
    (guards : OptionalForGuards G F condition) :
    ForTestObserver G F n condition :=
  match condition, guards with
  | .none, _ => absentForTestObserver G F n
  | .some ce, guards => presentForTestObserver G F n ce (guards n)

/-- Successful true-test adaptation preserves the full underlying guard run. -/
theorem presentForTest_guard_true {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (guard : GuardObserver G F n condition)
    (prior : List (EntryReferenceScope E)) (l l1 : Source.Locals E.layout Γ)
    (s after : Source.EMState E [])
    (run : ((presentForTestObserver G F n condition guard).observe prior l s).1=(.ok (true,l1),after)) :
    (guard.observe prior l s).1=(.ok (.val (.bool true),l1),after) := by
  cases actual : (guard.observe prior l s).1 with
  | mk result finalState =>
    cases result with
    | error error =>
      simp only [presentForTestObserver,observePresentForTest,actual] at run
      cases run
    | ok pair =>
      rcases pair with ⟨value,locals⟩
      cases value with
      | val value =>
        cases value with
        | memRef h _ => cases h
        | storRef h _ => cases h
        | cdRef h _ _ => cases h
        | bool flag =>
          simp only [presentForTestObserver,observePresentForTest,actual] at run
          cases run
          rfl

/-- Captures produced by the actual first body survive every later outcome. -/
theorem optionalForIteration_body_scopes {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ)
    (post : Source.ROptExpr E Γ) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (guards : OptionalForGuards G F condition)
    (posts : OptionalForPosts G F post)
    (bodies : ∀ i, StatementObserver G F i nps ph body)
    (prior : List (EntryReferenceScope E)) (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (test : ((optionalForTestObserver G F n condition guards).observe prior l s).1=(.ok (true,l1),after))
    (scope) (member : scope∈((bodies n).observe
      ((optionalForTestObserver G F n condition guards).observe prior l s).2 l1 after).2) :
    scope∈((optionalForIterationObserver G F (n+1) nps ph condition post body guards posts bodies).observe prior l s).2 := by
  cases condition with
  | none =>
    change ((.ok (true,l),s) : Except Source.Halt (Bool × Source.Locals E.layout Γ) × Source.EMState E [])=
      (.ok (true,l1),after) at test
    cases test
    cases post with
    | none => exact unconditionalForIteration_body_scopes G F n nps ph body bodies prior l s scope member
    | some pe =>
      exact observeForPostIteration_body_scopes G F n nps ph .none pe body
        (absentForTestObserver G F) bodies posts prior l l s s rfl scope member
  | some ce =>
    have raw := presentForTest_guard_true G F n ce (guards n) prior l l1 s after test
    cases post with
    | none => exact guardedForIteration_body_scopes G F n nps ph ce body guards bodies prior l l1 s after raw scope member
    | some pe =>
      exact observeForPostIteration_body_scopes G F n nps ph (.some ce) pe body
        (fun i => presentForTestObserver G F i ce (guards i)) bodies posts prior l l1 s after test scope member

end Solidity.Yul.Views
