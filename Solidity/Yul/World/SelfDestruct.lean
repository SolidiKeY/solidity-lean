import Solidity.Yul.World.Lifecycle
/-! Composition of existing EIP-6780 balance and scheduling preparations.
No new Source/world implementation or account reachability law is assumed.
Creation flags must be justified by the creation producer; this leaf does not
terminate a callee or classify its Option refusal as an EVM halt. Execution
rollback below does not restore lifecycle flags: their entry snapshot remains
a frame-completion obligation. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → SPath → STy}
/-- Local lifecycle leaf only: termination/world reachability remain external. -/
def selfDestruct (entry : Lifecycle D L T) (static : Bool) (a beneficiary : Address) :
    Option (Lifecycle D L T) :=
  if static then none else do
    let execution ← destructTransfer entry.execution (entry.created a) a beneficiary
    ({entry with execution := execution}).schedule false a
theorem selfDestruct_success_iff (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address) :
    selfDestruct entry static a beneficiary = some out ↔
      static = false ∧ ∃ execution,
        destructTransfer entry.execution (entry.created a) a beneficiary = some execution ∧
        out = {entry with execution := execution, doomed := fun b => if b = a then entry.doomed b || entry.created b else entry.doomed b} := by
  constructor
  · intro completed
    cases static with
    | true => cases completed
    | false =>
      cases transferred : destructTransfer entry.execution (entry.created a) a beneficiary with
      | none =>
        simp only [selfDestruct, Bool.false_eq_true, ↓reduceIte, transferred,
          bind, Option.bind_none] at completed
        cases completed
      | some execution =>
        simp only [selfDestruct, Bool.false_eq_true, ↓reduceIte, transferred,
          bind, Option.bind_some, Lifecycle.schedule, Option.some.injEq] at completed
        exact ⟨rfl,execution,rfl,completed.symm⟩
  · rintro ⟨rfl,execution,transferred,rfl⟩
    simp only [selfDestruct, Bool.false_eq_true, ↓reduceIte, transferred,
      bind, Option.bind_some, Lifecycle.schedule]
theorem selfDestruct_static (entry : Lifecycle D L T) (a beneficiary : Address) :
    selfDestruct entry true a beneficiary = none := rfl

theorem selfDestruct_rollback (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out)
    (receiver caller : Address) (value : Word) (input : Bytes) (frameStatic : Bool) :
    (entry.execution.enter receiver caller value input frameStatic).rollback out.execution = entry.execution := by
  obtain ⟨_,execution,transferred,equal⟩ := (selfDestruct_success_iff entry out static a beneficiary).mp completed
  subst out
  exact rollback_destructTransfer entry.execution execution (entry.created a) a beneficiary transferred
    receiver caller value input frameStatic

theorem selfDestruct_finish_fresh (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out) (fresh : entry.created a = true) :
    out.finish.execution.world.accounts a = Account.empty (L a) := by
  obtain ⟨_,execution,transferred,equal⟩ := (selfDestruct_success_iff entry out static a beneficiary).mp completed
  subst out
  simp only [Lifecycle.finish, ↓reduceIte, fresh, Bool.or_true, Bool.true_and]

theorem selfDestruct_finish_old (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out) (old : entry.created a = false) :
    out.finish.execution.world.accounts a = out.execution.world.accounts a := by
  obtain ⟨_,execution,transferred,equal⟩ := (selfDestruct_success_iff entry out static a beneficiary).mp completed
  subst out
  simp only [Lifecycle.finish, old, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
end Solidity.Yul.World
