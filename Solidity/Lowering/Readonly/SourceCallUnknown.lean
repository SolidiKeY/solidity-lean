import Solidity.Lowering.Readonly.SourceCallPrefix
import Solidity.Lowering.Readonly.CallSupportEffects

/-! Exact unknown-call Source branch, including nonzero debit and live rollback.
No payment rule, capture provenance, native frame or whole-world equality. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open StaticJournal
variable {E : Env}
namespace CallPrefix
def entered (state : St E) (frame : Fr) (receiver : Address) (value : Word)
    (input : Bytes) (requested : Bool) : St E :=
  {state with events := state.events ++ [.call receiver value input (requested || frame.static)]}

def followup (global : Glob E) (frame : Fr) (n : Nat) (receiver : Address)
    (value : Word) (input : Bytes) (requested : Bool)
    (mark : Nat × Nat × Heap E.layout) : EM E [] Outcome := do
  emitEvent (.call receiver value input (requested || frame.static))
  let out ← envLoop global n (frame.depth+1) (requested || frame.static)
  match out with
  | .revert _ => do rollbackTo mark; pure out
  | .success _ => pure out

def unknown (global : Glob E) (frame : Fr) (n : Nat) (receiver : Address)
    (value : Word) (input : Bytes) (requested : Bool) : EM E [] Outcome := do
  let mark ← Source.mark
  if value.val ≠ 0 then
    if !(← debit frame.this value) then return .revert []
  followup global frame n receiver value input requested mark

theorem followup_history (global : Glob E) (frame : Fr) (n : Nat) (smaller : At global n)
    (receiver : Address) (value : Word) (input : Bytes) (requested : Bool)
    (entry current : St E)
    (prior : History entry.ex (requested || frame.static) current.ex) :
    History entry.ex (requested || frame.static)
      ((followup global frame n receiver value input requested
        (entry.ex.journal.length,entry.logs.length,entry.heap)).run (L0 E,current)).2.2.ex := by
  have loopHistory := smaller.envLoop (frame.depth+1) (requested || frame.static) (L0 E)
    (entered current frame receiver value input requested)
  have eventRun : (emitEvent (.call receiver value input (requested || frame.static)) : EM E [] Unit).run
      (L0 E,current) = (.ok (), (L0 E,entered current frame receiver value input requested)) := rfl
  simp only [followup, Hoare.run_bind, eventRun]
  rcases loopRun : (envLoop global n (frame.depth+1) (requested || frame.static)).run
      (L0 E,entered current frame receiver value input requested) with ⟨result,locals,final⟩
  cases locals
  rw [loopRun] at loopHistory
  have joined : History entry.ex (requested || frame.static) final.ex :=
    JournalLeaves.chain loopHistory entry.ex prior
  cases result with
  | error halt => exact joined
  | ok out =>
    cases out with
    | success bytes => exact joined
    | revert bytes =>
      change History entry.ex (requested || frame.static)
        (final.ex.undoN (final.ex.journal.length-entry.ex.journal.length))
      rw [HistoryRollback.rewind joined]
      exact .start _ _

theorem unknown_effect (global : Glob E) (frame : Fr) (n : Nat) (smaller : At global n)
    (receiver : Address) (value : Word) (input : Bytes) (requested : Bool) :
    Effect (requested || frame.static) (unknown global frame n receiver value input requested) := by
  intro locals state
  cases locals
  have markRun : (Source.mark : EM E [] _).run (L0 E,state) =
    (.ok (state.ex.journal.length,state.logs.length,state.heap),(L0 E,state)) := rfl
  simp only [unknown, Hoare.run_bind, markRun]
  by_cases nonzero : value.val ≠ 0
  · rw [if_pos nonzero, Hoare.run_bind]
    have debitHistory := JournalLeaves.debit_history frame.this value (L0 E) state (requested || frame.static)
    rcases debitRun : (debit frame.this value : EM E [] Bool).run (L0 E,state) with ⟨result,locals,debited⟩
    cases locals
    rw [debitRun] at debitHistory
    cases result with
    | error halt => exact debitHistory
    | ok enough =>
      cases enough with
      | false => exact debitHistory
      | true => exact followup_history global frame n smaller receiver value input requested state debited debitHistory
  · simp only [nonzero, ↓reduceIte]
    exact followup_history global frame n smaller receiver value input requested state state (.start _ _)

theorem unknown_run (global : Glob E) (frame : Fr) (n : Nat) (receiver : Address)
    (value : Word) (input : Bytes) (requested : Bool) (state : St E)
    (depth : ¬ frame.depth ≥ 1024)
    (guard : (frame.static && decide (value.val ≠ 0)) = false)
    (lookup : (instanceAt global receiver : EM E [] _).run (L0 E,state) =
      (.ok none,(L0 E,state))) :
    (callAddr global frame (n+1) receiver value input requested).run (L0 E,state) =
      (unknown global frame n receiver value input requested).run (L0 E,state) := by
  dsimp only [ExceptT.run] at lookup
  rw [callAddr]
  simp only [depth,guard,Bool.false_eq_true,↓reduceIte]
  simp only [unknown,followup,Source.mark,EM.st,bind,pure,
    ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,
    MonadStateOf.get,liftM,monadLift,
    MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,lookup]
  by_cases nonzero : value.val ≠ 0
  all_goals first
  | rfl
  | simp only [nonzero,↓reduceIte,bind,pure,ExceptT.bindCont, StateT.bind,StateT.pure,StateT.get,StateT.map]
    rfl
end CallPrefix
end Solidity.Lowering.Readonly.SourceHistory
