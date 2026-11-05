import SolidityBridge.Yul.LoopClassification
/-! Concrete extension of the existing target block selector with loops.
Uses the same Block/Selected/Slice definitions and constructs classification
with each successful selection. Source admission and source loop compilation
remain separate; existing selectors and their refusals are unchanged. -/
namespace SolidityBridge.Yul.LoopSelection
open Solidity Backend
open SolidityBridge.Yul

/-- Recursively select existing target blocks, including classified loops. -/
def selectBlock : (block : Backend.Block) → Option (OccurrenceControl.Selected block)
  | .code p => (OccurrenceSelection.selectCode p).map OccurrenceControl.leaf
  | .seq a b => do
      let first ← selectBlock a
      let second ← selectBlock b
      pure (OccurrenceControl.combine first second)
  | .ite c a b => do
      let test ← OccurrenceSelection.selectCode c
      let yes ← selectBlock a
      let no ← selectBlock b
      pure (OccurrenceControl.branch test yes no)
  | .loop c b => do
      let test ← OccurrenceSelection.selectCode c
      let body ← selectBlock b
      pure ⟨LoopRealization.realization c b test body.realization,
        LoopClassification.classified c b test body.realization body.classified⟩
end SolidityBridge.Yul.LoopSelection
