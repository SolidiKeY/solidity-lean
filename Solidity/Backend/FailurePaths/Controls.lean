import Solidity.Backend.FailurePaths.Returns
import Solidity.Backend.Failure.Composition
import Solidity.Lowering.V08.LiteralFailureControls
import Solidity.Lowering.V08.BoolErrorCompleteness
import Solidity.Lowering.V08.BoolErrorControls

/-!
# Inhabited G38 statement and payload controls

These use the published populated source state and nonempty byte machine.
Both pipeline modes execute actual source statements and checked terminal code.
They do not assert frontend admission, a full EVM run or a physical world map.
-/
namespace Solidity.Backend.FailurePaths.Controls
open Source
open Lowering.V08.SourceCustomErrorControls
open Lowering.V08.LiteralFailureLowering

def message : Roadmap.Bytes := [0, 255, 7]
def machine := Lowering.V08.LiteralFailureControls.machine
def tail : Backend.Program := [.op .ADD]
def statement : RStmt E [] false .body [.bool] [.bool] := .expr (requireFalse message)
def program : Backend.Program := Failure.emit 5 (.custom (errorData message))

theorem statement_agreement (pipeline : Roadmap.Pipeline) :
    compileExpression 5 (requireFalse (E := E) (Γ := [.bool]) message) = some program ∧
    StatementReverts (global pipeline) frame 7 statement locals populated populated (errorData message) ∧
    Failure.Slice.checkedRun (program ++ tail) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory 5 (errorData message)},
        some (.revert (errorData message))) := by
  obtain ⟨compiled, source, _, target⟩ := literal_statement (global pipeline) frame 0 5
    (requireFalse message) (.custom (errorData message)) rfl locals populated
  exact ⟨compiled, source, target tail machine
    (Lowering.V08.LiteralFailureControls.reason_fits message (by decide +kernel)) (by decide +kernel)⟩

/-- A true guard is a successful source statement and is refused by this
failure-only compiler; it must not be silently replaced with REVERT. -/
theorem true_guard_refused :
    compileExpression 5 (.builtin .require (.cons (.bool true) .nil) rfl : RExpr E [.bool] (.tuple [])) = none := rfl

theorem true_guard_runs (pipeline : Roadmap.Pipeline) :
    (execS (global pipeline) frame 7 0 none
      (.expr (.builtin .require (.cons (.bool true) .nil) rfl) :
        RStmt E [] false .body [.bool] [.bool]) locals).run (Source.L0 E, populated) =
      (.ok (.normal locals), (Source.L0 E, populated)) := rfl

theorem timeout_retained (pipeline : Roadmap.Pipeline) :
    (execS (global pipeline) frame 0 0 none statement locals).run (Source.L0 E, populated) =
      (.error .timeout, (Source.L0 E, populated)) := rfl

theorem effectful_refused :
    compileExpression 5 Lowering.V08.LiteralFailureControls.effectful = none := rfl

def ops : List (Source.Op E.layout E.lay E.lay) :=
  [.account self (fun a => {a with storage := a.storage.write saved (.bool false)}),
   .transient self (fun t => t.write scratch (.bool false))]

theorem dirty_world :
    ((populated.ex.run ops).world.accounts self).storage.read saved = some (.bool false) ∧
    ((populated.ex.run ops).transient.cells self).read scratch = some (.bool false) ∧
    (populated.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (populated.ex.transient.cells self).read scratch = some (.bool true) := ⟨rfl, rfl, rfl, rfl⟩

theorem dirty_statement_unwinds (pipeline : Roadmap.Pipeline) :
    let reached := {populated with ex := populated.ex.run ops}
    StatementReverts (global pipeline) frame 7 statement locals reached reached (errorData message) ∧
    (populated.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback reached.ex = populated.ex ∧
    Failure.Local.execute
      (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex machine)) 5
      (.custom (errorData message)) (MemoryOps.Physical.worldJournal reached.ex machine) =
      some (MemoryOps.Physical.worldJournal populated.ex machine, .revert (errorData message)) :=
  literal_world_unwind (global pipeline) frame 0 5 (requireFalse message) (.custom (errorData message))
    rfl locals populated ops machine machine
    (Lowering.V08.LiteralFailureControls.reason_fits message (by decide +kernel)) (by decide +kernel)

/-- The encoder premise is inhabited with the actual Boolean source encoder. -/
theorem return_encoding_inhabited :
    Premises.EncodingAt frame 0
      (Lowering.V08.BoolErrorLowering.values (E := E) [true, false]).toR populated populated
      (Lowering.V08.BoolErrorLowering.encoded [true, false]) :=
  boolean_encoding frame 0 [true, false] populated

theorem assert_agreement (pipeline : Roadmap.Pipeline) :
    StatementReverts (global pipeline) frame 7 (.expr assertFalse) locals populated populated (panicData .assert) ∧
    Failure.Slice.checkedRun (Failure.emit 5 (panicInput .assert) ++ tail) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory 5 (panicData .assert)},
        some (.revert (panicData .assert))) := by
  obtain ⟨_, source, _, target⟩ := literal_statement (global pipeline) frame 0 5
    (assertFalse (E := E) (Γ := [.bool])) (panicInput .assert) rfl locals populated
  constructor
  · simpa only [panic_bytes] using source
  · simpa only [panic_bytes, panic_observation] using target tail machine
      (by simpa only [panic_bytes] using Lowering.V08.LiteralFailureControls.panic_fits .assert)
      (by decide +kernel)

def customStmt : RStmt E [] false .body [.bool] [.bool] :=
  Lowering.V08.BoolErrorLowering.statement (Lowering.V08.BoolErrorControls.declaration 3)
    Lowering.V08.BoolErrorControls.bits Lowering.V08.BoolErrorControls.typed_three

def customCode (pipeline : Roadmap.Pipeline) : Backend.Program :=
  Lowering.V08.BoolErrorLowering.emit (global pipeline) (Lowering.V08.BoolErrorControls.declaration 3)
    Lowering.V08.BoolErrorControls.bits 8

theorem custom_agreement (pipeline : Roadmap.Pipeline) :
    compileStatement (global pipeline) 8 customStmt = some (customCode pipeline) ∧
    StatementReverts (global pipeline) frame 7 customStmt locals populated populated
      (Lowering.V08.BoolErrorLowering.payload (global pipeline) (Lowering.V08.BoolErrorControls.declaration 3)
        Lowering.V08.BoolErrorControls.bits) ∧
    Failure.Slice.checkedRun (customCode pipeline ++ tail) machine =
      some ({machine with memory := (Failure.Slice.putBytes machine.memory 8
        (Lowering.V08.BoolErrorLowering.payload (global pipeline) (Lowering.V08.BoolErrorControls.declaration 3)
          Lowering.V08.BoolErrorControls.bits))},
        some (.revert (Lowering.V08.BoolErrorLowering.payload (global pipeline)
          (Lowering.V08.BoolErrorControls.declaration 3) Lowering.V08.BoolErrorControls.bits))) := by
  refine ⟨compile_custom_selected (global pipeline) 8 customStmt (customCode pipeline) ?_, ?_, ?_⟩
  · exact Lowering.V08.BoolErrorCompleteness.emit_complete (global pipeline) 8 _ _ _
  · exact Lowering.V08.BoolErrorLowering.source_run (global pipeline) frame 0
      (Lowering.V08.BoolErrorControls.declaration 3) Lowering.V08.BoolErrorControls.bits
      Lowering.V08.BoolErrorControls.typed_three locals populated
  · exact Lowering.V08.BoolErrorLowering.emitted_run (global pipeline) _ _ 8 tail machine
      (Lowering.V08.BoolErrorControls.fits pipeline) (by decide +kernel)

theorem skip_refused (pipeline : Roadmap.Pipeline) :
    compileStatement (global pipeline) 5 (.skip : RStmt E [] false .body [.bool] [.bool]) = none := rfl

theorem returned_after_dirty_prefix :
    Failure.Local.execute
      (Failure.Local.save (MemoryOps.Physical.worldJournal empty.ex machine)) 5
      (.returned (Lowering.V08.BoolErrorLowering.encoded [true, false]))
      (MemoryOps.Physical.worldJournal populated.ex machine) =
      some (MemoryOps.Physical.worldJournal populated.ex
        {machine with memory := (Failure.Slice.putBytes machine.memory 5
          (Lowering.V08.BoolErrorLowering.encoded [true, false]))},
        .success (Lowering.V08.BoolErrorLowering.encoded [true, false])) :=
  (encoded_return frame 0 5 (Lowering.V08.BoolErrorLowering.values (E := E) [true, false]).toR
    populated populated empty _ return_encoding_inhabited machine machine
    (by unfold Failure.Fits; decide +kernel) (by decide +kernel)).2.2

theorem return_is_not_revert :
    Failure.Slice.checkedRun (Failure.emit 5 (.returned message)) machine ≠
      Failure.Slice.checkedRun (Failure.emit 5 (.custom message)) machine :=
  Failure.return_revert_execution_distinct 5 message machine (by unfold Failure.Fits; decide +kernel) (by decide +kernel)

/-- Runtime observations accompany, rather than replace, the kernel theorems. -/
def sourceObservation (pipeline : Roadmap.Pipeline) : Option Roadmap.Bytes :=
  match (execS (global pipeline) frame 7 0 none statement locals).run (Source.L0 E, populated) |>.1 with
  | .error (.revert bytes) => some bytes
  | _ => none

def compiledObservation : Option Roadmap.Outcome :=
  match Failure.Slice.checkedRun (program ++ tail) machine with
  | some (_, result) => result
  | none => none

def sourceResult (pipeline : Roadmap.Pipeline) (stmt : RStmt E [] false .body [.bool] [.bool]) :
    Option Roadmap.Outcome :=
  match (execS (global pipeline) frame 7 0 none stmt locals).run (Source.L0 E, populated) |>.1 with
  | .error (.revert bytes) => some (.revert bytes)
  | _ => none

def targetResult (code : Backend.Program) : Option Roadmap.Outcome :=
  match Failure.Slice.checkedRun (code ++ tail) machine with
  | some (_, result) => result
  | none => none

#eval (sourceResult .legacy (.expr assertFalse), targetResult (Failure.emit 5 (panicInput .assert)))
#eval (sourceResult .viaIR (.expr assertFalse), targetResult (Failure.emit 5 (panicInput .assert)))
#eval (sourceResult .legacy (.expr revertBare), targetResult (Failure.emit 5 .empty))
#eval (sourceResult .viaIR (.expr revertBare), targetResult (Failure.emit 5 .empty))
#eval (sourceResult .legacy customStmt, targetResult (customCode .legacy))
#eval (sourceResult .viaIR customStmt, targetResult (customCode .viaIR))
#eval (Source.encodeVals frame 0 false
  (Lowering.V08.BoolErrorLowering.values (E := E) [true, false]).toR : EM E [] _).run
    (Source.L0 E, populated) |>.1
#eval targetResult (Failure.emit 5 (.returned (Lowering.V08.BoolErrorLowering.encoded [true, false])))

#eval sourceObservation .legacy
#eval sourceObservation .viaIR
#eval compiledObservation
#print axioms statement_agreement
#print axioms dirty_statement_unwinds
#print axioms return_encoding_inhabited
end Solidity.Backend.FailurePaths.Controls
