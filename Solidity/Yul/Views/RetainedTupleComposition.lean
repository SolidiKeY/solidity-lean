import Solidity.Yul.Views.RetainedTupleSequence

/-! Observers are indexed by actual Source item sequences and horizons. Their
projection and inherited-scope laws do not assert producer completeness. Tuple
prefix composition uses an observer's actual tail result, retaining captures
through errors and scope restoration. -/
namespace Solidity.Yul.Views

/-- A dependency contract for observing a particular actual Source execution.
No coverage field or general producer instance is assumed. -/
structure ItemsObserver {E Γ Γ' R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (body : Source.RItems E R M k Γ Γ') where
  observe : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
    (Except Source.Halt (Source.Out E.layout Γ Γ') × Source.EMState E []) × List (EntryReferenceScope E)
  source : ∀ prior l s, (observe prior l s).1=(Source.execItems G F n nps ph body l).run s
  prior : ∀ prior l s scope, scope∈prior → scope∈(observe prior l s).2

/-- The existing tuple prefix adapter supplies a concrete observer. Its raw
Source tail remains uninstrumented. -/
def tupleItemsObserver {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types)
    (rest : Source.RItems E R M k Γ Γ') :
    ItemsObserver G F n nps ph (.stmt (.expr (.tuple es)) rest) where
  observe := captureTupleItems G F n nps ph es rest
  source := captureTupleItems_source G F n nps ph es rest
  prior := captureTupleItems_prior G F n nps ph es rest

/-- Observe a tuple prefix and, on normal completion, the actual tail. -/
def observeTupleThen {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types)
    (rest : Source.RItems E R M k Γ Γ') (tail : ItemsObserver G F n nps ph rest)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ') × Source.EMState E []) × List (EntryReferenceScope E) :=
  let first := captureTupleStatement G F n es prior l s
  match first.1.1 with
  | .error error => ((.error error,first.1.2),first.2)
  | .ok (.normal l1) =>
    let next := tail.observe first.2 l1 first.1.2
    let result := match next.1.1 with
      | .error error => (.error error,next.1.2)
      | .ok out => (Source.EM.lift (out.up Γ) : Source.EM E [] (Source.Out E.layout Γ Γ')).run next.1.2
    (result,next.2)
  | .ok (.brk l1) => ((.ok (.brk l1),first.1.2),first.2)
  | .ok (.cont l1) => ((.ok (.cont l1),first.1.2),first.2)
  | .ok (.ret l1) => ((.ok (.ret l1),first.1.2),first.2)

theorem observeTupleThen_source {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types)
    (rest : Source.RItems E R M k Γ Γ') (tail : ItemsObserver G F n nps ph rest)
    (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeTupleThen G F n nps ph es rest tail prior l s).1=
      (Source.execItems G F (n+1) nps ph (.stmt (.expr (.tuple es)) rest) l).run s := by
  unfold observeTupleThen
  dsimp only
  rw [Source.execItems, Source.Hoare.run_bind]
  rw [← captureTupleStatement_source G F n nps ph es prior l s]
  cases first : (captureTupleStatement G F n es prior l s).1 with
  | mk result after =>
    cases result with
    | error error => rfl
    | ok out =>
      cases out with
      | normal l1 =>
        dsimp only
        rw [Source.Hoare.run_bind, ← tail.source]
        cases next : (tail.observe (captureTupleStatement G F n es prior l s).2 l1 after).1 with
        | mk result after => cases result <;> rfl
      | brk l1 => rfl
      | cont l1 => rfl
      | ret l1 => rfl

/-- Every scope captured by the prefix survives all observed tail outcomes. -/
theorem observeTupleThen_prefix {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types)
    (rest : Source.RItems E R M k Γ Γ') (tail : ItemsObserver G F n nps ph rest)
    (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (scope)
    (member : scope∈(captureTupleStatement G F n es prior l s).2) :
    scope∈(observeTupleThen G F n nps ph es rest tail prior l s).2 := by
  unfold observeTupleThen
  dsimp only
  cases first : (captureTupleStatement G F n es prior l s).1.1 with
  | error error => exact member
  | ok out =>
    cases out with
    | normal l1 => exact tail.prior _ _ _ scope member
    | brk l1 => exact member
    | cont l1 => exact member
    | ret l1 => exact member

/-- A concrete composed observer; the supplied tail contract stays explicit. -/
def tupleThenObserver {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types)
    (rest : Source.RItems E R M k Γ Γ') (tail : ItemsObserver G F n nps ph rest) :
    ItemsObserver G F (n+1) nps ph (.stmt (.expr (.tuple es)) rest) where
  observe := observeTupleThen G F n nps ph es rest tail
  source := observeTupleThen_source G F n nps ph es rest tail
  prior := fun prior l s scope member => observeTupleThen_prefix G F n nps ph es rest tail prior l s scope
    (captureTupleStatement_prior G F n es prior l s scope member)

/-- Normal prefix completion passes its captured scopes and actual state into
exactly the supplied tail observer, including when the tail halts. -/
theorem observeTupleThen_normal_scopes {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types)
    (rest : Source.RItems E R M k Γ Γ') (tail : ItemsObserver G F n nps ph rest)
    (prior) (l l1 : Source.Locals E.layout Γ) (s after : Source.EMState E [])
    (normal : (captureTupleStatement G F n es prior l s).1=(.ok (.normal l1),after)) :
    (observeTupleThen G F n nps ph es rest tail prior l s).2=
      (tail.observe (captureTupleStatement G F n es prior l s).2 l1 after).2 := by
  simp only [observeTupleThen, normal]

end Solidity.Yul.Views
