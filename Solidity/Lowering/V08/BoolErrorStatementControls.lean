import Solidity.Lowering.V08.BoolErrorStatement
import Solidity.Lowering.V08.BoolErrorControls

namespace Solidity.Lowering.V08.BoolErrorStatementControls
open Solidity Source Backend BoolErrorStatement BoolErrorControls SourceCustomErrorControls

def statement := BoolErrorLowering.statement (Γ:=SourceExternalPhaseControls.ctx)
 (declaration 3) bits typed_three

theorem selected (pipeline : Roadmap.Pipeline) :
 emitStatement (global pipeline) 8 statement =
 some (BoolErrorLowering.emit (global pipeline) (declaration 3) bits 8) := by rfl

theorem selected_empty (pipeline : Roadmap.Pipeline) :
 emitStatement (global pipeline) 8
 (BoolErrorLowering.statement (Γ:=[]) (declaration 0) [] typed_empty) =
 some (BoolErrorLowering.emit (global pipeline) (declaration 0) [] 8) := by rfl

/-- A valid source-local argument is refused by this literal-only adapter. -/
def localStatement : RStmt E [] false .body [.bool] [.bool] :=
 .revertError (declaration 1) (declaration_typed E [true])
 (.cons (.local .here) rfl .nil)

theorem local_refused (pipeline : Roadmap.Pipeline) :
 emitStatement (global pipeline) 8 localStatement = none := by rfl

theorem nonerror_refused (pipeline : Roadmap.Pipeline) :
 emitStatement (global pipeline) 8 (.skip : RStmt E [] false .body [] []) = none := by rfl

/-- Applied soundness on the populated caller: the selected statement supplies
its error declaration and literal arguments. Target Fits/stack remain explicit
in the reusable consequence; the existing fixture discharges both below. -/
def client (pipeline : Roadmap.Pipeline) :=
 selected_correct (global pipeline) frame 0 8 statement
 (BoolErrorLowering.emit (global pipeline) (declaration 3) bits 8)
 (selected pipeline) caller populated

theorem concrete_target (pipeline : Roadmap.Pipeline) :
 Failure.Slice.checkedRun
  ((emitStatement (global pipeline) 8 statement).getD [] ++ suffix) machine =
 some ({machine with memory := Failure.Slice.putBytes machine.memory 8 (BoolErrorLowering.payload (global pipeline) (declaration 3) bits)},
  some (.revert (BoolErrorLowering.payload (global pipeline) (declaration 3) bits))) := by
 rw [selected]
 exact (BoolErrorControls.combined pipeline).2

#print axioms client
#print axioms concrete_target
#print axioms BoolErrorStatement.selected_witness
#print axioms BoolErrorStatement.selected_correct
#print axioms selected
#print axioms selected_empty
#print axioms local_refused
#print axioms nonerror_refused
end Solidity.Lowering.V08.BoolErrorStatementControls
