import Solidity.Lowering.V08.LiteralFailureChoiceDecode
import Solidity.Lowering.V08.LiteralFailureCalldataDecodeControls
import Solidity.Lowering.V08.LiteralFailureStorageDecodeControls

namespace Solidity.Lowering.V08.LiteralFailureChoiceDecodeControls
open Solidity Source LiteralFailureChoiceDecode SourceCustomErrorControls
open LiteralFailureCalldataDecodeControls

def context : RCtx := .bool :: .bytes .calldata :: .bytes .calldata :: SourceExternalPhaseControls.ctx

def caller (condition : Bool) (off len : Nat) : Locals E.layout context :=
 .cons (.bool condition) (.cons (.cdRef rfl 4 32) (.cons (.cdRef rfl off len) SourceExternalPhaseControls.caller))

def expression (swap : Bool) : RExpr E context (.int u8) :=
 .abiDecode (τs:=[.int u8])
  (.cond (.local .here)
   (if swap then .local (.there (.there .here)) else .local (.there .here))
   (if swap then .local (.there .here) else .local (.there (.there .here)))) rfl rfl

theorem unselected_missing (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) (F (data 7)) 3 (expression false)).run (caller true 1000 32,populated) =
 (.ok (.val (.int 7 (by decide +kernel))),(caller true 1000 32,populated)) := by rfl

theorem selected_missing (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) (F (data 7)) 3 (expression false)).run (caller false 1000 32,populated) =
 (.error (.revert []),(caller false 1000 32,populated)) := by rfl

theorem swapped_branches (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) (F (data 7)) 3 (expression true)).run (caller true 1000 32,populated) =
 (.error (.revert []),(caller true 1000 32,populated)) := by rfl

theorem equal_aliases (pipeline : Roadmap.Pipeline) (condition : Bool) :
 (evalE (global pipeline) (F (data 7)) 3 (expression false)).run (caller condition 4 32,populated) =
 (.ok (.val (.int 7 (by decide +kernel))),(caller condition 4 32,populated)) := by
 cases condition <;> rfl

theorem exhaustion (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) (F (data 7)) 2 (expression false)).run (caller false 1000 32,populated) =
 (.error .timeout,(caller false 1000 32,populated)) := by rfl

def generic_client (pipeline : Roadmap.Pipeline) (n : Nat) {H : HeapTy} :=
 calldata_ok (H:=H) (types:=[.int u8]) (global pipeline) (F (data 7)) n
  (.here : Source.Idx context .bool) (.there .here) (.there (.there .here)) rfl

namespace MemoryClient

def context : RCtx := .bool :: .bytes .memory :: .bytes .memory :: SourceExternalPhaseControls.ctx
def state : St E := {populated with heap := (populated.heap.alloc ⟨.bytes .memory,.bytes (wordBytes (toWord 7))⟩).1}
def caller (condition : Bool) : Locals E.layout context :=
 .cons (.bool condition) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) SourceExternalPhaseControls.caller))
def expression : RExpr E context (.int u8) :=
 .abiDecode (τs:=[.int u8]) (.cond (.local .here) (.local (.there .here)) (.local (.there (.there .here)))) rfl rfl

theorem success (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 3 expression).run (caller true,state) =
 (.ok (.val (.int 7 (by decide +kernel))),(caller true,state)) := by rfl

theorem selected_short (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 3 expression).run (caller false,state) =
 (.error (.revert []),(caller false,state)) := by rfl
end MemoryClient

namespace StorageClient
open LiteralFailureStorageDecodeControls

def context : RCtx := [.bool,.bytes .storage,.bytes .storage,.bytes .memory,.bool]
def locals : Locals environment.layout context :=
 .cons (.bool true) (.cons (.storRef rfl path) (.cons (.storRef rfl path) LiteralFailureStorageDecodeControls.caller))
def expression : RExpr environment context .bool :=
 .abiDecode (τs:=[.bool]) (.cond (.local .here) (.local (.there .here)) (.local (.there (.there .here)))) rfl rfl

theorem equal_aliases_revert (pipeline : Roadmap.Pipeline) :
 (evalE (LiteralFailureStorageDecodeControls.global pipeline) LiteralFailureStorageDecodeControls.frame 6 expression).run
  (locals,LiteralFailureStorageDecodeControls.populated) =
 (.error (.revert []),(locals,LiteralFailureStorageDecodeControls.populated)) := by rfl
end StorageClient

#eval String.intercalate "\n" ([data 7,wordBytes (toWord 7)].map render)
#eval LiteralFailureStorageDecodeControls.observe_copy 4 LiteralFailureStorageDecodeControls.populated

#print axioms choice_ok
#print axioms calldata_ok
#print axioms memory_ok
#print axioms storage_ok
#print axioms generic_client
#print axioms unselected_missing
#print axioms selected_missing
#print axioms swapped_branches
#print axioms equal_aliases
#print axioms exhaustion
#print axioms MemoryClient.success
#print axioms MemoryClient.selected_short
#print axioms StorageClient.equal_aliases_revert
end Solidity.Lowering.V08.LiteralFailureChoiceDecodeControls
