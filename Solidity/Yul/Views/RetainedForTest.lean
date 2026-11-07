import Solidity.Yul.Views.RetainedGuardObserver

/-! Exact optional-test observation for Source.forIter. An absent test runs no
expression and is true even at horizon zero. A present test reuses the actual
guard observer and getV. Scope retention is separate from completeness. -/
namespace Solidity.Yul.Views

/-- The actual optional-test computation used by Source.forIter. -/
def forTestEvaluation {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.ROptBool E Γ) (l : Source.Locals E.layout Γ) :
    Source.EM E [] (Bool × Source.Locals E.layout Γ) :=
  match condition with
  | .none => pure (true,l)
  | .some ce => do
    let (cv,l1) ← Source.EM.sub l (Source.evalE G F n ce)
    match ← Source.getV cv with
    | .bool b => pure (b,l1)

structure ForTestObserver {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.ROptBool E Γ) where
  observe : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
    (Except Source.Halt (Bool × Source.Locals E.layout Γ) × Source.EMState E []) × List (EntryReferenceScope E)
  source : ∀ prior l s, (observe prior l s).1=
    (forTestEvaluation G F n condition l).run s
  prior : ∀ prior l s scope, scope∈prior → scope∈(observe prior l s).2

def absentForTestObserver {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) :
    ForTestObserver G F n (.none (Γ:=Γ)) where
  observe := fun prior l s => ((.ok (true,l),s),prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def observePresentForTest {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (condition : Source.RExpr E Γ .bool)
    (observer : GuardObserver G F n condition) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Bool × Source.Locals E.layout Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let guard := observer.observe prior l s
  let result := match guard.1.1 with
    | .error error => (.error error,guard.1.2)
    | .ok (.val (.bool b),l1) => (.ok (b,l1),guard.1.2)
  (result,guard.2)

theorem observePresentForTest_source {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (condition : Source.RExpr E Γ .bool)
    (observer : GuardObserver G F n condition) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observePresentForTest G F n condition observer prior l s).1=
      ((do let (cv,l1) ← Source.EM.sub l (Source.evalE G F n condition)
           match ← Source.getV cv with
           | .bool b => pure (b,l1)) : Source.EM E [] (Bool × Source.Locals E.layout Γ)).run s := by
  unfold observePresentForTest
  dsimp only
  rw [Source.Hoare.run_bind,← observer.source]
  cases guard : (observer.observe prior l s).1 with
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
        | bool b => rfl

def presentForTestObserver {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (condition : Source.RExpr E Γ .bool)
    (observer : GuardObserver G F n condition) : ForTestObserver G F n (.some condition) where
  observe := observePresentForTest G F n condition observer
  source := observePresentForTest_source G F n condition observer
  prior := observer.prior

end Solidity.Yul.Views
