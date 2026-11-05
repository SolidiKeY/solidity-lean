import Solidity.Backend.Passes.ReferenceCallCaptureFailure
import Solidity.Backend.Passes.ReferenceCallReadbackControls

namespace Solidity.Backend.Passes.ReferenceCallReadback.FailureControls
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3CallProducerRef.Tuple.Controls
open Solidity.Backend.Passes.ReferenceCallReadback.Controls

def bad : Val C Δ .uint := .readMem
  (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl)))
def bc : CompiledVal 1 selected.checked.frag bad := (compileVal 1 selected.checked.frag bad).get (by decide +kernel)
theorem bad_source : bad.evalT output.st = .error .revert := by
  have actual : (match bad.evalT output.st with
      | .error .revert => true | _ => false) = true := by
    unfold output
    decide +kernel
  generalize bad.evalT output.st = result at actual ⊢
  cases result with
  | ok v => cases actual
  | error halt => cases halt <;> cases actual <;> rfl

def capture := CapturedValueStability.captureStage (.user "badReturnedAliasRead") bad bc
def code := (V3CallProducerRef.plan selected 16 16).code ++ capture.code

def application := capture_revert_iff
  (body := V3CallProducerRef.Tuple.Controls.body) (f := "tupleAlias") (L := 1) (frame := 64)
  form chosen 16 16 flags (entered (wmod 0)) output source_run
  (.user "badReturnedAliasRead") bad bc (by decide)

theorem reached : ∃ addresses,
    StateRepr 1 1 64 selected.checked.frag output.st addresses returned ∧
    BaseExtends caller.H bases addresses ∧
    GrowsAllocator 1 64 1 caller bases initial output.st addresses returned ∧
    returned.mem 16 = w[20] ∧ Footprint.Words 16 20 initial returned ∧ ∀ tail,
      capture.Input 1 64 addresses output.st (appendTail returned tail) ∧
      run (V3CallProducerRef.plan selected 16 16).code (appendTail initial tail) =
        .ok (appendTail returned tail) 0 ∧
      (run code (appendTail initial tail) = .revert ↔ bad.evalT output.st = .error .revert) := by
  obtain ⟨actual,addresses,hcall,repr,_,ext,growth,cursor,words,runs⟩ := application
  have same : actual = returned := (Evm.Out.ok.inj (hcall.symm.trans returned_run)).1
  subst actual
  refine ⟨addresses,repr,ext,?_,cursor,words,runs⟩
  simpa only [cost] using growth

theorem joined_failure (tail : List Word) :
    run code (appendTail initial tail) = .revert ∧
    (Prog.cons (Stmt.call "tupleAlias" V3CallProducerRef.ArrayControls.args (.rets binders)
      V3CallProducerRef.Tuple.Controls.body)
      (.cons (.declLocal .uint (.user "badReturnedAliasRead") (some bad)) .nil)).run caller = .error .revert := by
  obtain ⟨_,_,_,_,_,_,runs⟩ := reached
  exact ⟨((runs tail).2.2).mpr bad_source,
    source_capture_revert (body := V3CallProducerRef.Tuple.Controls.body)
      (f := "tupleAlias") (args := V3CallProducerRef.ArrayControls.args) (ret := .rets binders) output source_run (.user "badReturnedAliasRead") bad bad_source⟩

theorem returned_observations (tail : List Word) :
    (cells.map (appendTail returned tail).mem,(appendTail returned tail).stack) =
      ([w[131],w[128],w[0],w[128],w[7],w[128],w[20],w[128],w[0],w[0],w[99],w[1],w[0],w[0]],
        w[77] :: tail) := by
  apply Prod.ext
  · change cells.map returned.mem =
      [w[131],w[128],w[0],w[128],w[7],w[128],w[20],w[128],w[0],w[0],w[99],w[1],w[0],w[0]]
    unfold cells returned
    decide +kernel
  · change returned.stack ++ tail = _
    have hs : returned.stack = [w[77]] := by unfold returned; decide +kernel
    rw [hs]
    rfl

/-- A free physical slot may retain an old argument. Capture must overwrite it;
there is no zero-initialization premise for the returned context's next cell. -/
theorem wrong_zero_capture_cell : returned.mem 5 ≠ w[0] := by
  unfold returned
  decide +kernel

/-- At the same reached input, replacing the bad alias read by the real local
receiver succeeds: the call itself was not the failure stage. -/
theorem wrong_failure_stage (tail : List Word) :
    run vc.code (appendTail returned tail) = .ok ((appendTail returned tail).push w[7]) 0 := by
  obtain ⟨_,repr,_,_,_,_,_⟩ := reached
  obtain ⟨word,represented,actual⟩ := value_success_tail vc repr evaluated (returned.stack ++ tail)
  have same : word = w[7] := Restored.value_unique represented (ReprV.uint_of rfl)
  subst word
  exact actual

end Solidity.Backend.Passes.ReferenceCallReadback.FailureControls
