import Solidity.Backend.FailurePaths.BooleanReturn
import Solidity.Backend.FailurePaths.Controls

/-!
# Executed literal return-statement controls

The actual hidden Boolean slot changes from old to returned value. The source
observer extracts retVals from the actual returned locals and encodes in the
actual reached state. The target is the published checked terminal slice.
-/
namespace Solidity.Backend.FailurePaths.BooleanReturnControls
open Source
open Lowering.V08.SourceCustomErrorControls

def code (value : Bool) : Backend.Program :=
  Failure.emit 5 (.returned (BooleanReturn.payload value))

theorem selected (value : Bool) :
    BooleanReturn.compile 5 (BooleanReturn.statement (E := E) (Γ := [.bool]) value) = some (code value) := rfl

theorem run_agreement (pipeline : Roadmap.Pipeline) (old value : Bool) :
    (execS (global pipeline) frame 7 0 none (BooleanReturn.statement value)
      (BooleanReturn.locals old)).run (Source.L0 E, populated) =
      (.ok (.ret (BooleanReturn.locals value)), (Source.L0 E, populated)) ∧
    retVals (BooleanReturn.locals (E := E) value) 0 [.bool] = .ok (BooleanReturn.values value) ∧
    (encodeVals frame 0 false (BooleanReturn.values value) : EM E [] _).run
      (Source.L0 E, populated) = (.ok (BooleanReturn.payload value), (Source.L0 E, populated)) ∧
    Failure.Slice.checkedRun (code value ++ Controls.tail) Controls.machine =
      some ({Controls.machine with memory := (Failure.Slice.putBytes Controls.machine.memory 5
        (BooleanReturn.payload value))}, some (.success (BooleanReturn.payload value))) := by
  refine ⟨BooleanReturn.source_run (global pipeline) frame 0 old value populated,
    BooleanReturn.returned_values value, BooleanReturn.encoded_values frame 0 value populated, ?_⟩
  exact Failure.checkedRun_emit_suffix 5 (.returned (BooleanReturn.payload value)) Controls.tail Controls.machine
    (by cases value <;> unfold Failure.Fits <;> decide +kernel) (by decide +kernel)

/-- A runtime local is outside this literal selector even though source
execution succeeds. This is helper refusal, not rejection by the source. -/
def localReturn : RStmt E [.bool] false .body [.bool] [.bool] :=
  .retVal rfl (.local .here) rfl

theorem local_refused : BooleanReturn.compile 5 localReturn = none := rfl

theorem local_source (pipeline : Roadmap.Pipeline) (old : Bool) :
    (execS (global pipeline) frame 7 0 none localReturn (BooleanReturn.locals old)).run
      (Source.L0 E, populated) = (.ok (.ret (BooleanReturn.locals old)), (Source.L0 E, populated)) := rfl

def sourceObservation (pipeline : Roadmap.Pipeline) (old value : Bool) : Option Roadmap.Bytes :=
  match (execS (global pipeline) frame 7 0 none (BooleanReturn.statement value)
      (BooleanReturn.locals old)).run (Source.L0 E, populated) with
  | (.ok (.ret returned), (_, reached)) =>
    match retVals returned 0 [.bool] with
    | .error _ => none
    | .ok vals =>
      match (encodeVals frame 0 false vals : EM E [] _).run (Source.L0 E, reached) |>.1 with
      | .ok bytes => some bytes
      | .error _ => none
  | _ => none

#eval sourceObservation .legacy false true
#eval sourceObservation .viaIR false true
#eval Controls.targetResult (code true)
#eval sourceObservation .legacy true false
#eval sourceObservation .viaIR true false
#eval Controls.targetResult (code false)
#print axioms run_agreement
#print axioms local_refused
#print axioms local_source
end Solidity.Backend.FailurePaths.BooleanReturnControls
