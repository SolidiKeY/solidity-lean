import Solidity.Yul.Views.RetainedIfThenObserver
import Solidity.Yul.Views.RetainedComparisonProducers

/-! Guard observers retain producer scopes across actual Source.EM.sub.
Comparison guards reuse existing pipeline-ordered operand capture. Composition
retains those captures even when guard conversion halts before body execution.
No contract asserts general expression capture completeness. -/
namespace Solidity.Yul.Views

/-- Exact observation of the actual guard subcomputation, with captured scopes. -/
structure GuardObserver {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) where
  observe : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
    (Except Source.Halt (Source.RVal E.layout .bool × Source.Locals E.layout Γ) × Source.EMState E []) × List (EntryReferenceScope E)
  source : ∀ prior l s, (observe prior l s).1=(Source.EM.sub l (Source.evalE G F n condition) :
    Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s
  prior : ∀ prior l s scope, scope∈prior → scope∈(observe prior l s).2

theorem captureComparisonRun_prior {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ)
    (scope) (member : scope∈prior) : scope∈(captureComparisonRun G F n op left right prior s).2 := by
  cases n with
  | zero => exact captureRuntimeRun_prefix F prior _ s scope member
  | succ n =>
    apply captureComparisonRun_keeps_operands G F n op left right prior s scope
    cases n with
    | zero => exact List.mem_append_left _ member
    | succ n =>
      apply capturePairRun_first G F n left right prior s scope
      cases pipeline : G.pipeline <;> exact captureRuntimeRun_prefix F prior _ s scope member

/-- Retain the comparison's actual operand scopes while applying precisely
Source.EM.sub's local-frame projection, including error-local discard. -/
def captureComparisonGuard {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.RVal E.layout .bool × Source.Locals E.layout Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let raw := captureComparisonRun G F n op left right prior (l,s.2)
  let result := match raw.1.1 with
    | .error error => (.error error,(s.1,raw.1.2.2))
    | .ok value => (.ok (value,raw.1.2.1),(s.1,raw.1.2.2))
  (result,raw.2)

theorem captureComparisonGuard_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (captureComparisonGuard G F n op left right prior l s).1=
      (Source.EM.sub l (Source.evalE G F n (.compare op left right)) :
        Source.EM E [] (Source.RVal E.layout .bool × Source.Locals E.layout Γ)).run s := by
  unfold captureComparisonGuard
  dsimp only
  rw [captureComparisonRun_source]
  rcases s with ⟨outer,state⟩
  unfold Source.EM.sub
  dsimp only [ExceptT.run]
  cases actual : (Source.evalE G F n (.compare op left right)).run (l,state) with
  | mk result after =>
    dsimp only [ExceptT.run] at actual
    cases after
    cases result <;> simp only [ExceptT.mk,actual]

/-- The sub projection preserves the entire actual comparison scope list. -/
theorem captureComparisonGuard_scopes {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (captureComparisonGuard G F n op left right prior l s).2=
      (captureComparisonRun G F n op left right prior (l,s.2)).2 := rfl

/-- A concrete comparison guard observer, with no assumed coverage field. -/
def comparisonGuardObserver {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) : GuardObserver G F n (.compare op left right) where
  observe := captureComparisonGuard G F n op left right
  source := captureComparisonGuard_source G F n op left right
  prior := fun prior l s scope member => captureComparisonRun_prior G F n op left right prior (l,s.2) scope member

def observeGuardedIfThen {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (guardObserver : GuardObserver G F n condition)
    (observer : StatementObserver G F n nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let guard := guardObserver.observe prior l s
  match guard.1.1 with
  | .error error => ((.error error,guard.1.2),guard.2)
  | .ok (.val (.bool true),l1) => closeStatementRun (observer.observe guard.2 l1 guard.1.2)
  | .ok (.val (.bool false),l1) => ((.ok (.normal l1),guard.1.2),guard.2)

theorem observeGuardedIfThen_source {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (guardObserver : GuardObserver G F n condition)
    (observer : StatementObserver G F n nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeGuardedIfThen G F n nps ph condition body guardObserver observer prior l s).1=
      (Source.execS G F (n+1) nps ph (.ifThen condition body) l).run s := by
  unfold observeGuardedIfThen
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
          · rfl
          · change (closeStatementRun (observer.observe (guardObserver.observe prior l s).2 l1 after)).1=
              ((do let out ← Source.execS G F n nps ph body l1; Source.EM.lift out.close) :
                Source.EM E [] (Source.Out E.layout Γ Γ)).run after
            unfold closeStatementRun
            dsimp only
            rw [Source.Hoare.run_bind, ← observer.source]
            cases arm : (observer.observe (guardObserver.observe prior l s).2 l1 after).1 with
            | mk result finalState => cases result <;> rfl

/-- Every scope captured inside the actual guard survives guard failure,
false selection, or arbitrary subsequent body outcomes. -/
theorem observeGuardedIfThen_guard_scopes {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (guardObserver : GuardObserver G F n condition)
    (observer : StatementObserver G F n nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (scope)
    (member : scope∈(guardObserver.observe prior l s).2) :
    scope∈(observeGuardedIfThen G F n nps ph condition body guardObserver observer prior l s).2 := by
  unfold observeGuardedIfThen
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
          · exact observer.prior _ l1 after scope member

/-- Guard failure preserves both the actual error/state and captured inventory. -/
theorem observeGuardedIfThen_error {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (guardObserver : GuardObserver G F n condition)
    (observer : StatementObserver G F n nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s after : Source.EMState E []) (error)
    (run : (guardObserver.observe prior l s).1=(.error error,after)) :
    observeGuardedIfThen G F n nps ph condition body guardObserver observer prior l s=
      ((.error error,after),(guardObserver.observe prior l s).2) := by
  simp only [observeGuardedIfThen,run]

/-- Both contracts are explicit; the comparison instance above is proved from
actual operand capture rather than supplied as a completeness assumption. -/
def guardedIfThenStatementObserver {E Γ Γ₁ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.RExpr E Γ .bool)
    (body : Source.RStmt E R M k Γ Γ₁) (guardObserver : GuardObserver G F n condition)
    (observer : StatementObserver G F n nps ph body) :
    StatementObserver G F (n+1) nps ph (.ifThen condition body) where
  observe := observeGuardedIfThen G F n nps ph condition body guardObserver observer
  source := observeGuardedIfThen_source G F n nps ph condition body guardObserver observer
  prior := fun prior l s scope member => observeGuardedIfThen_guard_scopes G F n nps ph condition body
    guardObserver observer prior l s scope (guardObserver.prior prior l s scope member)

end Solidity.Yul.Views
