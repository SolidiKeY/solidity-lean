import Solidity.Lowering.V08.LiteralFailureEffectDecode
import Solidity.Lowering.V08.LiteralFailureChoiceDecodeControls

namespace Solidity.Lowering.V08.LiteralFailureEffectDecodeControls
open Solidity Source LiteralFailureEffectDecode SourceCustomErrorControls
abbrev context := LiteralFailureChoiceDecodeControls.context
abbrev caller := LiteralFailureChoiceDecodeControls.caller
abbrev F := LiteralFailureCalldataDecodeControls.F
abbrev data := LiteralFailureCalldataDecodeControls.data
abbrev u8 := LiteralFailureCalldataDecodeControls.u8

def expression (bit : Bool) : RExpr E context (.int u8) :=
 .abiDecode (τs:=[.int u8])
  (.cond (.assign (.local .here) (.bool bit)) (.local (.there .here))
   (.local (.there (.there .here)))) rfl rfl

theorem retained_failure (pipeline : Roadmap.Pipeline) (static : Bool) :
 (evalE (global pipeline) {(F (data 7)) with static:=static} 5 (expression false)).run
  (caller true 1000 32,populated) =
 (.error (.revert []),(caller false 1000 32,populated)) := by rfl

theorem retained_success (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) (F (data 7)) 5 (expression true)).run
  (caller false 1000 32,populated) =
 (.ok (.val (.int 7 (by decide +kernel))),(caller true 1000 32,populated)) := by rfl

theorem shared_alias (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) (F (data 7)) 5 (expression false)).run
  (caller true 4 32,populated) =
 (.ok (.val (.int 7 (by decide +kernel))),(caller false 4 32,populated)) := by rfl

theorem exhaustion_before_assignment (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) (F (data 7)) 3 (expression false)).run
  (caller true 1000 32,populated) =
 (.error .timeout,(caller true 1000 32,populated)) := by rfl

theorem stale_condition_rejected (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) {(F (data 7)) with static:=false} 5 (expression false)).run
  (caller true 1000 32,populated) ≠
 (.ok (.val (.int 7 (by decide +kernel))),(caller true 1000 32,populated)) := by
 rw [retained_failure]
 intro equality
 cases equality

def generic_client (pipeline : Roadmap.Pipeline) (n : Nat) {H : HeapTy} :=
 calldata_ok (H:=H) (types:=[.int u8]) (global pipeline) (F (data 7)) n
  (.here : Source.Idx context .bool) false (.there .here) (.there (.there .here)) rfl

namespace MemoryClient
abbrev BaseContext := LiteralFailureChoiceDecodeControls.MemoryClient.context
abbrev baseCaller := LiteralFailureChoiceDecodeControls.MemoryClient.caller
abbrev state := LiteralFailureChoiceDecodeControls.MemoryClient.state

def expression : RExpr E BaseContext (.int u8) :=
 .abiDecode (τs:=[.int u8]) (.cond (.assign (.local .here) (.bool false))
  (.local (.there .here)) (.local (.there (.there .here)))) rfl rfl

theorem retained_failure (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 5 expression).run (baseCaller true,state) =
 (.error (.revert []),(baseCaller false,state)) := by rfl
end MemoryClient

namespace StorageClient
open LiteralFailureStorageDecodeControls
abbrev context := LiteralFailureChoiceDecodeControls.StorageClient.context

def caller (bit : Bool) : Locals environment.layout context :=
 .cons (.bool bit) (.cons (.storRef rfl path)
  (.cons (.storRef rfl path) LiteralFailureStorageDecodeControls.caller))
def expression : RExpr environment context .bool :=
 .abiDecode (τs:=[.bool]) (.cond (.assign (.local .here) (.bool false))
  (.local (.there .here)) (.local (.there (.there .here)))) rfl rfl

theorem retained_failure (pipeline : Roadmap.Pipeline) :
 (evalE (LiteralFailureStorageDecodeControls.global pipeline)
  LiteralFailureStorageDecodeControls.frame 6 expression).run
  (caller true,LiteralFailureStorageDecodeControls.populated) =
 (.error (.revert []),(caller false,LiteralFailureStorageDecodeControls.populated)) := by rfl
end StorageClient

/-- Test-only lossless rendering, not a semantic definition or proof. -/
def observe (bit initial : Bool) (fuel : Nat) : String :=
 let output := (evalE (global .legacy) (F (data 7)) fuel (expression bit)).run
  (caller initial 1000 32,populated)
 let outcome := match output.1 with
  | .ok (.val (.int value _)) => "{\"ok\":" ++ toString value
  | .error (.revert bytes) => "{\"revert\":" ++ LiteralFailureCalldataDecodeControls.render bytes
  | .error .timeout => "{\"timeout\":true"
  | _ => "{\"other\":true"
 let condition := match output.2.1.get .here with | .bool b => b
 outcome ++ ",\"condition\":" ++ toString condition ++ "}"
#eval String.intercalate "\n" [observe false true 5,observe true false 5,observe false true 3]

#print axioms assign_run
#print axioms assign_ok
#print axioms choice
#print axioms assigned_choice
#print axioms calldata_ok
#print axioms memory_ok
#print axioms storage_ok
#print axioms retained_failure
#print axioms retained_success
#print axioms shared_alias
#print axioms exhaustion_before_assignment
#print axioms stale_condition_rejected
#print axioms generic_client
#print axioms MemoryClient.retained_failure
#print axioms StorageClient.retained_failure
end Solidity.Lowering.V08.LiteralFailureEffectDecodeControls
