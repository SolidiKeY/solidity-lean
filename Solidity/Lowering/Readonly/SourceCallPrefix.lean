import Solidity.Lowering.Readonly.SourceHistory
import Solidity.Lowering.Readonly.HistoryRollback
import Solidity.Source.Hoare

/-! Exact prefix of the existing known-instance Source call branch. These
balance-only histories are not payment admission or settlement rules. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open StaticJournal
variable {E : Env}
namespace CallPrefix
def fund (frame : Fr) (receiver : Address) (value : Word) : EM E [] Bool := do
  if receiver = frame.this then
    pure (decide (value.val ≤ ((← EM.st).ex.world.accounts receiver).balance.val))
  else
    match (← EM.st).ex.transfer frame.this receiver value with
    | some ex => EM.modSt fun s => { s with ex := ex }; pure true
    | none => pure false

def known (global : Glob E) (frame : Fr) (n : Nat) (receiver : Address)
    (value : Word) (input : Bytes) (requested : Bool) (code : String) : EM E [] Outcome := do
  let mark ← Source.mark
  let funded ← fund frame receiver value
  if !funded then return .revert []
  enterInstance global n receiver frame.this value input (requested || frame.static) code (frame.depth+1) mark

theorem fund_effect (mode : Bool) (frame : Fr) (receiver : Address) (value : Word) :
    Effect mode (fund (E := E) frame receiver value) := by
  intro locals state
  cases locals
  by_cases same : receiver = frame.this
  · simp only [fund, same, ↓reduceIte, EM.st, bind, pure, ExceptT.bind,
      ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind,
      StateT.pure, StateT.get, get, getThe, MonadStateOf.get, liftM,
      monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map]
    exact .start _ _
  · simp only [fund, same, ↓reduceIte, EM.st, EM.modSt, bind, pure, ExceptT.bind,
      ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind,
      StateT.pure, StateT.get, modify, modifyGet, get, getThe,
      MonadStateOf.get, MonadStateOf.modifyGet, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map]
    cases transfer : state.ex.transfer frame.this receiver value with
    | none => exact .start _ _
    | some final =>
      exact transfer_history state.ex final frame.this receiver value mode transfer

theorem known_run (global : Glob E) (frame : Fr) (n : Nat) (receiver : Address)
    (value : Word) (input : Bytes) (requested : Bool) (code : String) (state : St E)
    (depth : ¬ frame.depth ≥ 1024)
    (guard : (frame.static && decide (value.val ≠ 0)) = false)
    (lookup : (instanceAt global receiver : EM E [] _).run (L0 E, state) =
      (.ok (some code), (L0 E, state))) :
    (callAddr global frame (n+1) receiver value input requested).run (L0 E, state) =
      (known global frame n receiver value input requested code).run (L0 E, state) := by
  dsimp only [ExceptT.run] at lookup
  rw [callAddr]
  simp only [depth, guard, Bool.false_eq_true, ↓reduceIte]
  simp only [known, fund, Source.mark, EM.st, EM.modSt, bind, pure,
    ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk,
    StateT.bind, StateT.pure, StateT.get, modify, modifyGet,
    get, getThe, MonadStateOf.get, MonadStateOf.modifyGet, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, lookup]
  by_cases same : receiver = frame.this
  all_goals simp only [same, ↓reduceIte, bind, pure, ExceptT.bindCont,
    StateT.bind, StateT.pure, StateT.get, StateT.map]
  all_goals first
  | rfl
  | cases state.ex.transfer frame.this receiver value <;> rfl

theorem known_effect (global : Glob E) (frame : Fr) (n : Nat) (history : At global n)
    (receiver : Address) (value : Word) (input : Bytes) (requested : Bool) (code : String) :
    Effect (requested || frame.static) (known global frame n receiver value input requested code) := by
  intro locals state
  cases locals
  have fundedHistory := fund_effect (E := E) (requested || frame.static) frame receiver value (L0 E) state
  have markRun : (Source.mark : EM E [] _).run (L0 E, state) =
      (.ok (state.ex.journal.length, state.logs.length, state.heap), (L0 E, state)) := rfl
  simp only [known, Hoare.run_bind, markRun]
  rcases funding : (fund (E := E) frame receiver value).run (L0 E, state) with ⟨result, locals, final⟩
  cases locals
  rw [funding] at fundedHistory
  cases result with
  | error halt => exact fundedHistory
  | ok funded =>
    cases funded with
    | false => exact fundedHistory
    | true =>
      exact history.enterInstance receiver frame.this value input (requested || frame.static)
        code (frame.depth+1) state final fundedHistory
end CallPrefix
end Solidity.Lowering.Readonly.SourceHistory
