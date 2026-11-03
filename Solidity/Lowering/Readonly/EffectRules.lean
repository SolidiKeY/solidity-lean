import Solidity.Lowering.Readonly.SourceHistory

/-! Composition rules for the actual Source effect predicate. Catching a halt
keeps its reached state; it does not assert rollback. Inherited mode can be
forgotten only toward the parent mode, never strengthened to static. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ Γ' : RCtx} {α β : Type}

namespace Effect

theorem of_same_ex (mode : Bool) (m : EM E Γ α)
    (same : ∀ locals state, (m.run (locals, state)).2.2.ex = state.ex) : Effect mode m := by
  intro locals state
  rw [same]
  exact .start _ _

theorem bind (mode : Bool) (m : EM E Γ α) (k : α → EM E Γ β)
    (first : Effect mode m) (next : ∀ value, Effect mode (k value)) :
    Effect mode (m >>= k) := by
  intro locals state
  exact JournalLeaves.bind_history m k locals state mode (first locals state)
    (fun value locals state _ => next value locals state)

theorem sub (mode : Bool) (inner : Locals E.layout Γ') (m : EM E Γ' α)
    (h : Effect mode m) : Effect mode (EM.sub (Γ := Γ) inner m) := by
  intro locals state
  exact JournalLeaves.sub_history inner m locals state mode (h inner state)

theorem attempt (mode : Bool) (m : EM E Γ α) (h : Effect mode m) :
    Effect mode (EM.attempt m) := by
  intro locals state
  exact h locals state

theorem parent (mode requested : Bool) (m : EM E Γ α)
    (h : Effect (requested || mode) m) : Effect mode m := by
  intro locals state
  exact .child (.start _ _) requested (h locals state)

theorem pure (mode : Bool) (value : α) : Effect mode (Pure.pure value : EM E Γ α) :=
  of_same_ex mode _ (fun _ _ => rfl)

theorem halt (mode : Bool) (h : Halt) : Effect mode (EM.halt h : EM E Γ α) :=
  of_same_ex mode _ (fun _ _ => rfl)

theorem st (mode : Bool) : Effect mode (EM.st : EM E Γ (St E)) :=
  of_same_ex mode _ (fun _ _ => rfl)

theorem locals (mode : Bool) : Effect mode (EM.locals : EM E Γ (Locals E.layout Γ)) :=
  of_same_ex mode _ (fun _ _ => rfl)

theorem setLocals (mode : Bool) (values : Locals E.layout Γ) :
    Effect mode (EM.setLocals values : EM E Γ Unit) :=
  of_same_ex mode _ (fun _ _ => rfl)

end Effect
end Solidity.Lowering.Readonly.SourceHistory
