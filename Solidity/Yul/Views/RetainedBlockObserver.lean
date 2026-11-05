import Solidity.Yul.Views.RetainedTupleComposition

/-! Actual block and statement-sequence observers. Projection and inherited
scope preservation remain distinct from producer completeness. Blocks use
Source.Out.close, and sequencing uses Source.Out.up at the original contexts. -/
namespace Solidity.Yul.Views

/-- Observation contract for a particular actual Source statement. -/
structure StatementObserver {E Γ Γ' R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (stmt : Source.RStmt E R M k Γ Γ') where
  observe : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
    (Except Source.Halt (Source.Out E.layout Γ Γ') × Source.EMState E []) × List (EntryReferenceScope E)
  source : ∀ prior l s, (observe prior l s).1=(Source.execS G F n nps ph stmt l).run s
  prior : ∀ prior l s scope, scope∈prior → scope∈(observe prior l s).2

/-- Close a genuinely observed block using the owner's restoration operation. -/
def observeBlock {E Γ Γ' R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RItems E R M k Γ Γ')
    (inner : ItemsObserver G F n nps ph body) (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let result := inner.observe prior l s
  let closed := match result.1.1 with
    | .error error => (.error error,result.1.2)
    | .ok out => (Source.EM.lift out.close : Source.EM E [] (Source.Out E.layout Γ Γ)).run result.1.2
  (closed,result.2)

theorem observeBlock_source {E Γ Γ' R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RItems E R M k Γ Γ')
    (inner : ItemsObserver G F n nps ph body) (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeBlock G F n nps ph body inner prior l s).1=
      (Source.execS G F (n+1) nps ph (.block body) l).run s := by
  unfold observeBlock
  dsimp only
  rw [Source.execS, Source.Hoare.run_bind, ← inner.source]
  cases observed : (inner.observe prior l s).1 with
  | mk value after => cases value <;> rfl

/-- Closing a scope never discards its observed producer inventory, including
when actual restoration fails. -/
theorem observeBlock_scopes {E Γ Γ' R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RItems E R M k Γ Γ')
    (inner : ItemsObserver G F n nps ph body) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeBlock G F n nps ph body inner prior l s).2=(inner.observe prior l s).2 := rfl

def blockStatementObserver {E Γ Γ' R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RItems E R M k Γ Γ')
    (inner : ItemsObserver G F n nps ph body) :
    StatementObserver G F (n+1) nps ph (.block body) where
  observe := observeBlock G F n nps ph body inner
  source := observeBlock_source G F n nps ph body inner
  prior := inner.prior

/-- General typed statement/tail composition; early controls skip the tail. -/
def observeStatementThen {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (stmt : Source.RStmt E R M k Γ Γ₁)
    (rest : Source.RItems E R M k Γ₁ Γ₂) (first : StatementObserver G F n nps ph stmt)
    (tail : ItemsObserver G F n nps ph rest) (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ₂) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let observed := first.observe prior l s
  match observed.1.1 with
  | .error error => ((.error error,observed.1.2),observed.2)
  | .ok (.normal l1) =>
    let next := tail.observe observed.2 l1 observed.1.2
    let result := match next.1.1 with
      | .error error => (.error error,next.1.2)
      | .ok out => (Source.EM.lift (out.up Γ) : Source.EM E [] (Source.Out E.layout Γ Γ₂)).run next.1.2
    (result,next.2)
  | .ok (.brk l1) => ((.ok (.brk l1),observed.1.2),observed.2)
  | .ok (.cont l1) => ((.ok (.cont l1),observed.1.2),observed.2)
  | .ok (.ret l1) => ((.ok (.ret l1),observed.1.2),observed.2)

theorem observeStatementThen_source {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (stmt : Source.RStmt E R M k Γ Γ₁)
    (rest : Source.RItems E R M k Γ₁ Γ₂) (first : StatementObserver G F n nps ph stmt)
    (tail : ItemsObserver G F n nps ph rest) (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeStatementThen G F n nps ph stmt rest first tail prior l s).1=
      (Source.execItems G F (n+1) nps ph (.stmt stmt rest) l).run s := by
  unfold observeStatementThen
  dsimp only
  rw [Source.execItems, Source.Hoare.run_bind, ← first.source]
  cases observed : (first.observe prior l s).1 with
  | mk result after =>
    cases result with
    | error error => rfl
    | ok out =>
      cases out with
      | normal l1 =>
        dsimp only
        rw [Source.Hoare.run_bind, ← tail.source]
        cases next : (tail.observe (first.observe prior l s).2 l1 after).1 with
        | mk result after => cases result <;> rfl
      | brk l1 => rfl
      | cont l1 => rfl
      | ret l1 => rfl

/-- Prefix captures survive errors, controls and actual tail execution. -/
theorem observeStatementThen_prefix {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (stmt : Source.RStmt E R M k Γ Γ₁)
    (rest : Source.RItems E R M k Γ₁ Γ₂) (first : StatementObserver G F n nps ph stmt)
    (tail : ItemsObserver G F n nps ph rest) (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈(first.observe prior l s).2) :
    scope∈(observeStatementThen G F n nps ph stmt rest first tail prior l s).2 := by
  unfold observeStatementThen
  dsimp only
  cases observed : (first.observe prior l s).1.1 with
  | error error => exact member
  | ok out =>
    cases out with
    | normal l1 => exact tail.prior _ _ _ scope member
    | brk l1 => exact member
    | cont l1 => exact member
    | ret l1 => exact member

/-- Composition retains the original statement and actual tail indices. -/
def statementThenObserver {E Γ Γ₁ Γ₂ R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (stmt : Source.RStmt E R M k Γ Γ₁)
    (rest : Source.RItems E R M k Γ₁ Γ₂) (first : StatementObserver G F n nps ph stmt)
    (tail : ItemsObserver G F n nps ph rest) : ItemsObserver G F (n+1) nps ph (.stmt stmt rest) where
  observe := observeStatementThen G F n nps ph stmt rest first tail
  source := observeStatementThen_source G F n nps ph stmt rest first tail
  prior := fun prior l s scope member => observeStatementThen_prefix G F n nps ph stmt rest first tail prior l s scope
    (first.prior prior l s scope member)

end Solidity.Yul.Views
