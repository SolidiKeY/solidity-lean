import Solidity.Yul.Views.RetainedGuardObserver

/-! An observed loop test followed by a typed continuation. The continuation's
exact Source computation and inherited-scope law stay explicit. No synthetic
Source statement, scope close or new evaluator representation is introduced. -/
namespace Solidity.Yul.Views

def observeLoopTest {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (guardObserver : GuardObserver G F n condition)
    (next : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
      (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E))
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let guard := guardObserver.observe prior l s
  match guard.1.1 with
  | .error error => ((.error error,guard.1.2),guard.2)
  | .ok (.val (.bool false),l1) => ((.ok (.normal l1),guard.1.2),guard.2)
  | .ok (.val (.bool true),l1) => next guard.2 l1 guard.1.2

theorem observeLoopTest_source {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (guardObserver : GuardObserver G F n condition)
    (next : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
      (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E))
    (back : Source.Locals E.layout Γ → Source.EM E [] (Source.Out E.layout Γ Γ))
    (source : ∀ prior l s, (next prior l s).1=(back l).run s)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeLoopTest G F n condition guardObserver next prior l s).1=
      ((do let (cv,l1) ← Source.EM.sub l (Source.evalE G F n condition)
           match ← Source.getV cv with
           | .bool true => back l1
           | _ => pure (.normal l1)) : Source.EM E [] (Source.Out E.layout Γ Γ)).run s := by
  unfold observeLoopTest
  dsimp only
  rw [Source.Hoare.run_bind,← guardObserver.source]
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
          · rfl
          · exact source _ l1 after

/-- Captures produced by the test survive either outcome and the continuation. -/
theorem observeLoopTest_guard_scopes {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (guardObserver : GuardObserver G F n condition)
    (next : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
      (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E))
    (keeps : ∀ prior l s scope, scope∈prior → scope∈(next prior l s).2)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈(guardObserver.observe prior l s).2) :
    scope∈(observeLoopTest G F n condition guardObserver next prior l s).2 := by
  unfold observeLoopTest
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
          · exact member
          · exact keeps _ l1 after scope member

end Solidity.Yul.Views
