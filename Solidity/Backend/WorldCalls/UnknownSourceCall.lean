import Solidity.Backend.WorldCalls.SourceBridge
import Solidity.Lowering.Readonly.EnvironmentHistory
import Solidity.Lowering.Readonly.HistoryRollback

/-! Actual unknown-callee, zero-value source-call transport. Callback histories
remain explicit bounded source-child premises; no target runtime is assumed. -/
namespace Solidity.Backend.WorldCalls.UnknownSourceCall
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
variable {E : Env}

def entered (state : St E) (frame : Fr) (receiver : Address) (input : Bytes) (requested : Bool) : St E :=
  {state with events := state.events ++ [.call receiver ⟨0, by decide⟩ input (requested || frame.static)]}

private theorem run_bind {α β : Type} (m : EM E [] α) (k : α → EM E [] β)
    (x : Locals E.layout [] × St E) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error e, y) => (.error e, y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run m) _ x = _
  simp only [StateT.bind]
  rcases m.run x with ⟨r, y⟩
  cases r <;> rfl

/-- All actual environment outcomes and halts cross the same caller boundary.
Reverts retain their ordered bytes and execute rollback to the live call mark. -/
theorem transport (global : Glob E) (frame : Fr) (n : Nat)
    (receiver : Address) (input : Bytes) (requested : Bool) (state : St E)
    (depth : ¬ frame.depth ≥ 1024)
    (unknown : (instanceAt global receiver : EM E [] _).run (L0 E, state) =
      (.ok none, (L0 E, state))) :
    (callAddr global frame (n + 1) receiver ⟨0, by decide⟩ input requested).run (L0 E, state) =
      match (envLoop global n (frame.depth + 1) (requested || frame.static)).run
          (L0 E, entered state frame receiver input requested) with
      | (.error halt, reached) => (.error halt, reached)
      | (.ok (.success bytes), reached) => (.ok (.success bytes), reached)
      | (.ok (.revert bytes), reached) =>
          ((do rollbackTo (EnvironmentSteps.checkpoint state); pure (.revert bytes)) : EM E [] Outcome).run reached := by
  dsimp only [ExceptT.run] at unknown
  rw [callAddr]
  simp only [depth, ↓reduceIte, ne_eq, not_true_eq_false, decide_false, Bool.and_false, Bool.false_eq_true,
    run_bind]
  simp only [mark, EM.st, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.get, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    Functor.map, StateT.map, emitEvent, EM.modSt, StateT.modifyGet, modify, modifyGet, MonadStateOf.modifyGet,
    entered, EnvironmentSteps.checkpoint, unknown]
  cases h : (envLoop global n (frame.depth + 1) (requested || frame.static)).run
    (L0 E, entered state frame receiver input requested) with
  | mk result reached =>
    dsimp only [ExceptT.run, entered] at h
    rw [h]
    cases result with
    | error halt => rfl
    | ok out => cases out <;> rfl

/-- Successful unknown calls preserve the actual environment's final state. -/
theorem success (global : Glob E) (frame : Fr) (n : Nat)
    (receiver : Address) (input bytes : Bytes) (requested : Bool) (state final : St E)
    (depth : ¬ frame.depth ≥ 1024)
    (unknown : (instanceAt global receiver : EM E [] _).run (L0 E, state) = (.ok none, (L0 E, state)))
    (loop : (envLoop global n (frame.depth + 1) (requested || frame.static)).run
      (L0 E, entered state frame receiver input requested) = (.ok (.success bytes), (L0 E, final))) :
    (callAddr global frame (n + 1) receiver ⟨0, by decide⟩ input requested).run (L0 E, state) =
      (.ok (.success bytes), (L0 E, final)) := by
  rw [transport global frame n receiver input requested state depth unknown, loop]

/-- Real loop history discharges this successful unknown call's P2 history;
there is no no-callback assumption. Child histories are still bounded premises. -/
theorem success_history (global : Glob E) (frame : Fr) (n : Nat)
    (receiver : Address) (input bytes : Bytes) (requested : Bool) (state final : St E)
    (children : EnvironmentHistory.CallbackHistories global (requested || frame.static) n)
    (loop : (envLoop global n (frame.depth + 1) (requested || frame.static)).run
      (L0 E, entered state frame receiver input requested) = (.ok (.success bytes), (L0 E, final))) :
    StaticJournal.History state.ex (requested || frame.static) final.ex := by
  have history := EnvironmentHistory.loop global (requested || frame.static) n children
    (frame.depth + 1) (entered state frame receiver input requested)
  rw [loop] at history
  exact history

/-- Joint P3/P2 producer for an actual captured unknown zero-value call that
returns successfully. Child histories, inherited static mode and the source
execution remain exact; this does not cover the reverting branch's history. -/
theorem invocation_success {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
    (i : InvocationFrame.Invocation E Γ dn ps rs) (n : Nat) (bytes : Bytes) (final : St E)
    (horizon : i.horizon = n + 1) (zero : i.captured.value = ⟨0, by decide⟩)
    (depth : ¬ i.frame.depth ≥ 1024) (static : i.mode = true)
    (unknown : (instanceAt i.global i.captured.receiver : EM E [] _).run (L0 E, i.after.2) =
      (.ok none, (L0 E, i.after.2)))
    (children : EnvironmentHistory.CallbackHistories i.global i.mode n)
    (loop : (envLoop i.global n (i.frame.depth + 1) i.mode).run
      (L0 E, entered i.after.2 i.frame i.captured.receiver i.captured.input i.requested) =
        (.ok (.success bytes), (L0 E, final))) :
    i.RawAt (.ok (.success bytes)) final ∧ i.RuntimeFrames final := by
  refine ⟨?_, static, ?_⟩
  · simpa only [InvocationFrame.Invocation.RawAt, horizon, zero] using
      success i.global i.frame n i.captured.receiver i.captured.input bytes i.requested
        i.after.2 final depth unknown loop
  · exact success_history i.global i.frame n i.captured.receiver i.captured.input bytes
      i.requested i.after.2 final children loop

/-- All unknown zero-value call outcomes preserve a guarded Source history.
A completed revert rewinds the actual loop extension to its live entry; halts
retain the actual reached state. Callback histories remain explicit Source inputs. -/
theorem history (global : Glob E) (frame : Fr) (n : Nat)
    (receiver : Address) (input : Bytes) (requested : Bool) (state : St E)
    (depth : ¬ frame.depth ≥ 1024)
    (unknown : (instanceAt global receiver : EM E [] _).run (L0 E, state) =
      (.ok none, (L0 E, state)))
    (children : EnvironmentHistory.CallbackHistories global (requested || frame.static) n) :
    StaticJournal.History state.ex (requested || frame.static)
      ((callAddr global frame (n + 1) receiver ⟨0, by decide⟩ input requested).run (L0 E, state)).2.2.ex := by
  have loopHistory := EnvironmentHistory.loop global (requested || frame.static) n children
    (frame.depth + 1) (entered state frame receiver input requested)
  rw [transport global frame n receiver input requested state depth unknown]
  rcases run : (envLoop global n (frame.depth + 1) (requested || frame.static)).run
      (L0 E, entered state frame receiver input requested) with ⟨result, locals, final⟩
  rw [run] at loopHistory
  cases result with
  | error halt => exact loopHistory
  | ok out =>
    cases out with
    | success bytes => exact loopHistory
    | revert bytes =>
      change StaticJournal.History state.ex (requested || frame.static)
        (final.ex.undoN (final.ex.journal.length - state.ex.journal.length))
      have restored : final.ex.undoN (final.ex.journal.length - state.ex.journal.length) = state.ex :=
        HistoryRollback.rewind loopHistory
      rw [restored]
      exact .start _ _

/-- Same invocation, actual computed pre-decoder outcome and actual final
state. Success, revert, malformed return bytes and halts are not filtered.
The bounded callback-history producer is still an explicit Source obligation. -/
theorem evaluated_frame {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
    (i : InvocationFrame.Invocation E Γ dn ps rs) (n : Nat)
    (horizon : i.horizon = n + 1) (zero : i.captured.value = ⟨0, by decide⟩)
    (depth : ¬ i.frame.depth ≥ 1024) (static : i.mode = true)
    (unknown : (instanceAt i.global i.captured.receiver : EM E [] _).run (L0 E, i.after.2) =
      (.ok none, (L0 E, i.after.2)))
    (children : EnvironmentHistory.CallbackHistories i.global i.mode n) :
    i.RawAt (SourceBridge.evaluated i).1 (SourceBridge.evaluated i).2 ∧
      i.RuntimeFrames (SourceBridge.evaluated i).2 := by
  refine ⟨SourceBridge.evaluated_raw i, static, ?_⟩
  change StaticJournal.History i.after.2.ex i.mode
    ((callAddr i.global i.frame i.horizon i.captured.receiver i.captured.value
      i.captured.input i.requested).run (L0 E, i.after.2)).2.2.ex
  simpa only [horizon, zero] using history i.global i.frame n i.captured.receiver
    i.captured.input i.requested i.after.2 depth unknown children

end Solidity.Backend.WorldCalls.UnknownSourceCall
