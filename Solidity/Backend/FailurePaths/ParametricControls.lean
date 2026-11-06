import Solidity.Backend.FailurePaths.Parametric
import Solidity.Backend.FailurePaths.Controls

/-!
# Inhabited failures in a reference-returning body

The hidden return slot points at an actually allocated byte object. Neither the
literal failure nor the Boolean custom error reads or mutates that reference.
This is a statement-boundary check, not frontend/function-entry admission.
-/
namespace Solidity.Backend.FailurePaths.ParametricControls
open Source
open Lowering.V08.SourceCustomErrorControls

def locals : Locals E.layout [.bytes .memory] := .cons (.memRef rfl 0) .nil

def statement : RStmt E [.bytes .memory] false .body [.bytes .memory] [.bytes .memory] :=
  .expr (Lowering.V08.LiteralFailureLowering.requireFalse Controls.message)

theorem allocated_input :
    populated.heap.get 0 = some ⟨.bytes .memory, .bytes [0,255]⟩ ∧
    locals.get .here = .memRef rfl 0 := ⟨rfl, rfl⟩

theorem selected (pipeline : Roadmap.Pipeline) :
    Parametric.compile (global pipeline) 5 statement = some Controls.program := rfl

theorem reference_return_signature (pipeline : Roadmap.Pipeline) :
    ∃ fuel payload,
      Parametric.Reverts (global pipeline) frame fuel 0 statement locals populated payload ∧
      Emits Controls.program 5 (.custom payload) :=
  Parametric.selected_correct (global pipeline) frame 0 0 5 statement Controls.program
    (selected pipeline) locals populated

theorem exact_source (pipeline : Roadmap.Pipeline) :
    Parametric.Reverts (global pipeline) frame 7 0 statement locals populated (errorData Controls.message) := by
  have source := (literal_statement (global pipeline) frame 0 5
    (Lowering.V08.LiteralFailureLowering.requireFalse Controls.message)
    (.custom (errorData Controls.message)) rfl locals populated).2.1
  exact (Parametric.expression_tag (R := [.bytes .memory]) (global pipeline) frame 7 0
    (Lowering.V08.LiteralFailureLowering.requireFalse Controls.message) locals populated).trans source

def custom : RStmt E [.bytes .memory] false .body [.bytes .memory] [.bytes .memory] :=
  .revertError (Lowering.V08.BoolErrorControls.declaration 3)
    Lowering.V08.BoolErrorControls.typed_three
    (Lowering.V08.BoolErrorLowering.arguments Lowering.V08.BoolErrorControls.bits)

theorem custom_selected (pipeline : Roadmap.Pipeline) :
    Parametric.compile (global pipeline) 8 custom = some (Controls.customCode pipeline) :=
  Lowering.V08.BoolErrorCompleteness.emit_complete (global pipeline) 8 _ _ _

theorem custom_reference_signature (pipeline : Roadmap.Pipeline) :
    ∃ fuel payload,
      Parametric.Reverts (global pipeline) frame fuel 0 custom locals populated payload ∧
      Emits (Controls.customCode pipeline) 8 (.custom payload) :=
  Parametric.selected_correct (global pipeline) frame 0 0 8 custom (Controls.customCode pipeline)
    (custom_selected pipeline) locals populated

theorem true_guard_refused (pipeline : Roadmap.Pipeline) :
    Parametric.compile (global pipeline) 5
      (.expr (.builtin .require (.cons (.bool true) .nil) rfl) :
        RStmt E [.bytes .memory] false .body [.bytes .memory] [.bytes .memory]) = none := rfl

theorem timeout_retained (pipeline : Roadmap.Pipeline) :
    (execS (global pipeline) frame 0 0 none statement locals).run (Source.L0 E, populated) =
      (.error .timeout, (Source.L0 E, populated)) := rfl

def sourceObservation (pipeline : Roadmap.Pipeline)
    (stmt : RStmt E [.bytes .memory] false .body [.bytes .memory] [.bytes .memory]) :
    Option Roadmap.Outcome :=
  match (execS (global pipeline) frame 7 0 none stmt locals).run (Source.L0 E, populated) |>.1 with
  | .error (.revert bytes) => some (.revert bytes)
  | _ => none

#eval sourceObservation .legacy statement
#eval sourceObservation .viaIR statement
#eval Controls.targetResult Controls.program
#eval sourceObservation .legacy custom
#eval sourceObservation .viaIR custom
#eval Controls.targetResult (Controls.customCode .legacy)
#print axioms reference_return_signature
#print axioms exact_source
#print axioms custom_reference_signature
end Solidity.Backend.FailurePaths.ParametricControls
