import Solidity.Lowering.Readonly.EnvironmentSteps
import Solidity.Lowering.Readonly.Controls

/-! Inhabited source environment steps: an ordinary requested callback really
executes read-only code under inherited static mode; a forbidden value attempt
is refused; child timeout retains its exact state and does not answer. -/
namespace Solidity.Lowering.Readonly.EnvironmentControls
open Solidity.Source Solidity.Source.SemanticsExamples
open EnvironmentSteps

def global : Glob EB := Controls.readOrigin.global
def start : St EB := {sB with events := [.call ext (word 0) (selOf "ping()") true]}
def credited : St EB :=
  { entered start thisC ext (word 0) (selOf "cb()") false with
    ex := sB.ex.apply (.account thisC fun old => old.withBalance (word 0)) }

theorem read_child :
    (enterInstance global 28 thisC ext (word 0) (selOf "cb()") true "C" 2
      (checkpoint start)).run (L0 EB, credited) = (.ok (.success []), (L0 EB, credited)) := by rfl

theorem read_callback_step :
    (envLoop global 29 1 true).run (L0 EB, start) =
      (envLoop global 28 1 true).run (L0 EB, completed credited (.success [])) :=
  child_success global 28 1 true false start credited credited thisC ext (word 0)
    (selOf "cb()") "C" (.success []) (by rfl) (by decide) (by rfl) (by rfl) read_child

theorem read_callback_finishes :
    (envLoop global 29 1 true).run (L0 EB, start) =
      (.ok (.success []), (L0 EB, Controls.readFinal)) := by
  rw [read_callback_step, answer global 27 1 true _ (.success []) (by rfl)]
  rfl

/-- The ordinary requested child inherited static=true and was not suppressed. -/
theorem permitted_callback_present :
    Controls.readFinal.events.contains (.reentered (.success [])) = true := by decide +kernel

def valueStrategy : Solidity.Roadmap.Strategy := fun events =>
  if events.any (fun event => match event with | .reentered _ => true | _ => false)
  then .answer (.success [7]) else .reenter thisC ext (word 1) (selOf "cb()") false
def valueGlobal : Glob EB := {global with callee := valueStrategy}
def refusedFinal : St EB :=
  {completed (entered sB thisC ext (word 1) (selOf "cb()") false) (.revert []) with
    events := [.reenter thisC ext (word 1) (selOf "cb()") false,
      .reentered (.revert []), .answer (.success [7]) none]}

theorem value_refusal_continues :
    (envLoop valueGlobal 2 1 true).run (L0 EB, sB) =
      (.ok (.success [7]), (L0 EB, refusedFinal)) := by
  rw [refused valueGlobal 1 1 true false sB thisC ext (word 1) (selOf "cb()")
    (by rfl) (by decide)]
  rw [answer valueGlobal 0 1 true _ (.success [7]) (by rfl)]
  rfl

theorem child_exhaustion :
    (envLoop global 1 1 true).run (L0 EB, start) =
      (.error .timeout, (L0 EB, credited)) :=
  child_halt global 0 1 true false start credited credited thisC ext (word 0)
    (selOf "cb()") "C" .timeout (by rfl) (by decide) (by rfl) (by rfl) (by rfl)

end Solidity.Lowering.Readonly.EnvironmentControls
