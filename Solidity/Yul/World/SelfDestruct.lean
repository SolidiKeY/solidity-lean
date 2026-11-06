import Solidity.Yul.World.LifecycleAdapter
/-! Compatibility facade over the existing Lifecycle.destructKnown preparation.
No new Source/world implementation or account reachability law is assumed.
Creation flags must be justified by the creation producer; this leaf does not
terminate a callee or classify its Option refusal as an EVM halt. Execution
rollback below does not restore lifecycle flags; the existing
Lifecycle.rollbackDestruction provides local snapshot rollback. Reachable
frame/physical/observation composition remains a producer obligation. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → SPath → STy}
/-- Local lifecycle leaf only: termination/world reachability remain external. -/
abbrev selfDestruct (entry : Lifecycle D L T) (static : Bool) (a beneficiary : Address) :
    Option (Lifecycle D L T) :=
  entry.destructKnown static a beneficiary
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
        simp only [selfDestruct, Lifecycle.destructKnown, Bool.false_eq_true, ↓reduceIte, transferred,
          bind, Option.bind_none] at completed
        cases completed
      | some execution =>
        simp only [selfDestruct, Lifecycle.destructKnown, Bool.false_eq_true, ↓reduceIte, transferred,
          bind, Option.bind_some, Lifecycle.schedule, Option.some.injEq] at completed
        exact ⟨rfl,execution,rfl,completed.symm⟩
  · rintro ⟨rfl,execution,transferred,rfl⟩
    simp only [selfDestruct, Lifecycle.destructKnown, Bool.false_eq_true, ↓reduceIte, transferred,
      bind, Option.bind_some, Lifecycle.schedule]
theorem selfDestruct_static (entry : Lifecycle D L T) (a beneficiary : Address) :
    selfDestruct entry true a beneficiary = none := rfl

theorem selfDestruct_rollback (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out)
    (receiver caller : Address) (value : Word) (input : Bytes) (frameStatic : Bool) :
    (entry.execution.enter receiver caller value input frameStatic).rollback out.execution = entry.execution :=
  destructKnown_rollback entry out static a beneficiary completed receiver caller value input frameStatic

theorem selfDestruct_finish_fresh (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out) (fresh : entry.created a = true) :
    out.finish.execution.world.accounts a = Account.empty (L a) :=
  destructKnown_fresh_finish entry out static a beneficiary completed fresh

theorem selfDestruct_finish_old (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out) (old : entry.created a = false) :
    out.finish.execution.world.accounts a = out.execution.world.accounts a :=
  destructKnown_old_finish entry out static a beneficiary completed old

/-- Compatibility name is definitionally the existing producer operation. -/
theorem selfDestruct_eq_destructKnown (entry : Lifecycle D L T) (static : Bool) (a beneficiary : Address) :
    selfDestruct entry static a beneficiary = entry.destructKnown static a beneficiary := rfl
end Solidity.Yul.World
