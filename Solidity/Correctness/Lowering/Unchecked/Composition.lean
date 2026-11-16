import Solidity.Correctness.Lowering.Unchecked.Relation

/-!
# Composition of arithmetic/effect obligations

Guards the loss of failure poststates when lifting a pure arithmetic relation
through stateful evaluation. This is generic relation infrastructure, with no
claimed Source/model endpoint instance or partial-producer correspondence.
-/
namespace Solidity.Correctness.Lowering.Unchecked

open Solidity.Source

/-- One stateful bind law, usable for every rewritten arm. The continuation
is required only for related successful values. Both failure paths keep their
poststates, and no checked-panic or journal exception is excluded. -/
theorem effectRel_bind {S T α β γ δ : Type}
    {states : S → T → Prop} {values : α → β → Prop} {results : γ → δ → Prop}
    (source : ExceptT Halt (StateM S) α) (target : ExceptT Halt (StateM T) β)
    (left : α → ExceptT Halt (StateM S) γ) (right : β → ExceptT Halt (StateM T) δ)
    (related : EffectRel states values source.run target.run)
    (next : ∀ a b, values a b → EffectRel states results (left a).run (right b).run) :
    EffectRel states results (source >>= left).run (target >>= right).run := by
  intro s t h
  simp only [bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont]
  cases hs : source s with
  | mk sr ss =>
    cases ht : target t with
    | mk tr ts =>
      have initial : ResultRel values sr tr ∧ states ss ts := by
        simpa only [ExceptT.run, hs, ht] using related s t h
      cases sr with
      | error e =>
        cases tr with
        | ok b => exact False.elim initial.1
        | error f => exact initial
      | ok a =>
        cases tr with
        | error e => exact False.elim initial.1
        | ok b => exact next a b initial.1 ss ts initial.2

#print axioms effectRel_bind

end Solidity.Correctness.Lowering.Unchecked
