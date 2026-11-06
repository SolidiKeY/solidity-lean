import Solidity.Lowering.V08.BoolErrorCompleteness
import Solidity.Lowering.V08.BoolErrorControls

namespace Solidity.Lowering.V08.BoolErrorCompletenessControls
open Solidity Source Backend BoolErrorCompleteness BoolErrorControls SourceCustomErrorControls

/-- No successful-selection premise and no fixed argument count. -/
theorem uniform_selection (pipeline : Roadmap.Pipeline) (bs : List Bool) :
 BoolErrorStatement.emitStatement (global pipeline) 8
 (BoolErrorLowering.statement (Γ:=SourceExternalPhaseControls.ctx)
  (declaration bs.length) bs (declaration_typed E bs)) =
 some (BoolErrorLowering.emit (global pipeline) (declaration bs.length) bs 8) :=
 emit_complete (global pipeline) 8 _ bs _

theorem uniform_client (pipeline : Roadmap.Pipeline) (extra : Nat) (bs : List Bool)
 (room : Failure.Fits 8 (BoolErrorLowering.payload (global pipeline) (declaration bs.length) bs)) :
 (Source.execS (global pipeline) frame (bs.length+extra+4) 0 none
  (BoolErrorLowering.statement (declaration bs.length) bs (declaration_typed E bs)) caller).run
  (Source.L0 E,populated) =
  (.error (.revert (BoolErrorLowering.payload (global pipeline) (declaration bs.length) bs)),
   (Source.L0 E,populated)) ∧
 Failure.Slice.checkedRun
  ((BoolErrorStatement.emitStatement (global pipeline) 8
   (BoolErrorLowering.statement (Γ:=SourceExternalPhaseControls.ctx)
    (declaration bs.length) bs (declaration_typed E bs))).getD [] ++ suffix) machine =
 some ({machine with memory := Failure.Slice.putBytes machine.memory 8 (BoolErrorLowering.payload (global pipeline) (declaration bs.length) bs)},
  some (.revert (BoolErrorLowering.payload (global pipeline) (declaration bs.length) bs))) :=
 ⟨BoolErrorControls.uniform_client pipeline extra bs,
  emitted_complete (global pipeline) 8 _ bs _ suffix machine room (by decide +kernel)⟩

theorem populated_client (pipeline : Roadmap.Pipeline) :
 BoolErrorStatement.emitStatement (global pipeline) 8
 (BoolErrorLowering.statement (Γ:=SourceExternalPhaseControls.ctx) (declaration 3) bits typed_three) =
 some (BoolErrorLowering.emit (global pipeline) (declaration 3) bits 8) :=
 uniform_selection pipeline bits

def empty_selected (pipeline : Roadmap.Pipeline) := uniform_selection pipeline []
def sixty_four_selected (pipeline : Roadmap.Pipeline) :=
 uniform_selection pipeline (List.replicate 64 true)

#print axioms arguments_complete
#print axioms emit_complete
#print axioms emitted_complete
#print axioms uniform_selection
#print axioms uniform_client
#print axioms populated_client
#print axioms empty_selected
#print axioms sixty_four_selected
end Solidity.Lowering.V08.BoolErrorCompletenessControls
