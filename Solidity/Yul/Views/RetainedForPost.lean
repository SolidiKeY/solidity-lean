import Solidity.Yul.Views.RetainedForIteration
import Solidity.Yul.Views.RetainedTupleStatement

/-! Present post expressions retain captures before the actual Source sub
computation discards their runtime value. Exact continuation and inherited-scope
contracts are explicit; this is not a general for-iteration recursion producer. -/
namespace Solidity.Yul.Views

structure PostExpressionObserver {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (post : Source.RExpr E Γ σ) where
  observe : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
    (Except Source.Halt (Source.Locals E.layout Γ) × Source.EMState E []) × List (EntryReferenceScope E)
  source : ∀ prior l s, (observe prior l s).1=
    ((do pure (← Source.EM.sub l (Source.evalE G F n post)).2) : Source.EM E [] (Source.Locals E.layout Γ)).run s
  prior : ∀ prior l s scope, scope∈prior → scope∈(observe prior l s).2

def captureTuplePost {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Locals E.layout Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let raw := captureTupleRun G F n es prior (l,s.2)
  ((raw.1.1.map (fun _ => raw.1.2.1),(s.1,raw.1.2.2)),raw.2)

theorem captureTuplePost_source {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (captureTuplePost G F n es prior l s).1=
      ((do pure (← Source.EM.sub l (Source.evalE G F n (.tuple es))).2) :
        Source.EM E [] (Source.Locals E.layout Γ)).run s := by
  change (fun result : Except Source.Halt (Source.RVal E.layout (.tuple types)) × Source.EMState E Γ =>
    (result.1.map (fun _=>result.2.1),(s.1,result.2.2))) (captureTupleRun G F n es prior (l,s.2)).1=_
  rw [captureTupleRun_source,Source.Hoare.run_bind]
  unfold Source.EM.sub
  rcases s with ⟨outer,state⟩
  dsimp only [ExceptT.run]
  cases run : (Source.evalE G F n (.tuple es)).run (l,state) with
  | mk result after =>
    dsimp only [ExceptT.run] at run
    cases result <;> simp only [ExceptT.mk,run,Except.map] <;> rfl

/-- Tuple post captures are the same inventory as the corresponding actual
expression statement at one greater statement horizon. -/
theorem captureTuplePost_scopes {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (captureTuplePost G F n es prior l s).2=(captureTupleStatement G F (n+1) es prior l s).2 := rfl

/-- An actual head value survives a later post-argument failure. -/
theorem captureTuplePost_head {E Γ σ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (head : Source.RExpr E Γ σ) (tail : Source.RArgs E Γ types) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (after : Source.EMState E Γ) (value)
    (run : (Source.evalE G F n head).run (l,s.2)=(.ok value,after)) :
    runtimeScope F value∈(captureTuplePost G F (n+2) (.cons head tail) prior l s).2 :=
  captureTupleStatement_head G F n head tail prior l s after value run

def tuplePostObserver {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) : PostExpressionObserver G F n (.tuple es) where
  observe := captureTuplePost G F n es
  source := captureTuplePost_source G F n es
  prior := captureTupleStatement_prior G F (n+1) es

/-- Evaluate the actual post, then pass its reached locals/state and captures
into the actual next computation; an error retains the post inventory. -/
def observePostThen {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (post : Source.RExpr E Γ σ)
    (observer : PostExpressionObserver G F n post)
    (next : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
      (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E))
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let first := observer.observe prior l s
  match first.1.1 with
  | .error error => ((.error error,first.1.2),first.2)
  | .ok l1 => next first.2 l1 first.1.2

theorem observePostThen_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (post : Source.RExpr E Γ σ)
    (observer : PostExpressionObserver G F n post)
    (next : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
      (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E))
    (back : Source.Locals E.layout Γ → Source.EM E [] (Source.Out E.layout Γ Γ))
    (source : ∀ prior l s, (next prior l s).1=(back l).run s)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observePostThen G F n post observer next prior l s).1=
      ((do let l1 ← (do pure (← Source.EM.sub l (Source.evalE G F n post)).2)
           back l1) : Source.EM E [] (Source.Out E.layout Γ Γ)).run s := by
  unfold observePostThen
  dsimp only
  rw [Source.Hoare.run_bind,← observer.source]
  cases first : (observer.observe prior l s).1 with
  | mk result after =>
    cases result with
    | error error => rfl
    | ok l1 => exact source _ l1 after

theorem observePostThen_post_scopes {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (post : Source.RExpr E Γ σ)
    (observer : PostExpressionObserver G F n post)
    (next : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
      (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E))
    (keeps : ∀ prior l s scope, scope∈prior → scope∈(next prior l s).2)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈(observer.observe prior l s).2) :
    scope∈(observePostThen G F n post observer next prior l s).2 := by
  unfold observePostThen
  dsimp only
  cases first : (observer.observe prior l s).1 with
  | mk result after =>
    cases result with
    | error error => exact member
    | ok l1 => exact keeps _ l1 after scope member

end Solidity.Yul.Views
