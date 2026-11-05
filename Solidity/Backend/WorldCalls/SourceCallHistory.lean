import Solidity.Backend.WorldCalls.UnknownSourceCall
import Solidity.Lowering.Readonly.SourceCallPrefix

/-! Actual Source call histories from smaller-bound producers. Unknown zero-value
calls retain every outcome/halt and arbitrary permitted read-only callbacks.
This is not native provenance or Source-to-Core representation adequacy. -/
namespace Solidity.Backend.WorldCalls.SourceCallHistory
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
variable {E : Env}
theorem known (global : Glob E) (frame : Fr) (n : Nat) (smaller : SourceHistory.At global n)
    (receiver : Address) (value : Word) (input : Bytes) (requested : Bool)
    (code : String) (state : St E) (depth : ¬ frame.depth ≥ 1024)
    (guard : (frame.static && decide (value.val ≠ 0)) = false)
    (lookup : (instanceAt global receiver : EM E [] _).run (L0 E, state) =
      (.ok (some code), (L0 E, state))) :
    StaticJournal.History state.ex (requested || frame.static)
      ((callAddr global frame (n+1) receiver value input requested).run (L0 E, state)).2.2.ex := by
  rw [SourceHistory.CallPrefix.known_run global frame n receiver value input requested code state depth guard lookup]
  exact SourceHistory.CallPrefix.known_effect global frame n smaller receiver value input requested code (L0 E) state

theorem unknown_zero (global : Glob E) (frame : Fr) (n : Nat) (smaller : SourceHistory.At global n)
    (receiver : Address) (input : Bytes) (requested : Bool) (state : St E)
    (depth : ¬ frame.depth ≥ 1024)
    (lookup : (instanceAt global receiver : EM E [] _).run (L0 E, state) =
      (.ok none, (L0 E, state))) :
    StaticJournal.History state.ex (requested || frame.static)
      ((callAddr global frame (n+1) receiver ⟨0, by decide⟩ input requested).run (L0 E, state)).2.2.ex := by
  have loopHistory := smaller.envLoop (frame.depth+1) (requested || frame.static) (L0 E)
    (UnknownSourceCall.entered state frame receiver input requested)
  rw [UnknownSourceCall.transport global frame n receiver input requested state depth lookup]
  rcases run : (envLoop global n (frame.depth+1) (requested || frame.static)).run
      (L0 E, UnknownSourceCall.entered state frame receiver input requested) with ⟨result, locals, final⟩
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

theorem unknown_static_storage (global : Glob E) (frame : Fr) (n : Nat)
    (smaller : SourceHistory.At global n) (receiver : Address) (input : Bytes)
    (requested : Bool) (state : St E) (depth : ¬ frame.depth ≥ 1024)
    (lookup : (instanceAt global receiver : EM E [] _).run (L0 E, state) =
      (.ok none, (L0 E, state))) (static : (requested || frame.static) = true) :
    StaticJournal.SameStorage
      ((callAddr global frame (n+1) receiver ⟨0, by decide⟩ input requested).run (L0 E, state)).2.2.ex state.ex :=
  (unknown_zero global frame n smaller receiver input requested state depth lookup).storage static
end Solidity.Backend.WorldCalls.SourceCallHistory
