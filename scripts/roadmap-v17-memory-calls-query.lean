import Lean
import Solidity.Evm.MemoryCallExamples
-- V17_MEMORY_BODY
/-! Standalone above-core consumer; published intrinsic definitions are reused. -/
open Lean Lean.Meta Lean.Elab
open Solidity Solidity.Evm Solidity.Evm.Memory
namespace Solidity.Roadmap.V17.MemoryCalls

def privateName (suffix : String) : TermElabM Name := do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) => do
    let idx ← env.getModuleIdxFor? n
    if env.header.moduleNames[idx.toNat]! == `Solidity.Evm.MemoryCallExamples &&
        n.toString.endsWith ("." ++ suffix) then some n else none
  match names with
  | [n] => return n
  | _ => throwError "expected one published example constant: {suffix}"

elab "v17Example% " suffix:str : term => do
  mkConstWithFreshMVarLevels (← privateName suffix.getString)

private abbrev result := v17Example% "compiledMutation"
private abbrev program := v17Example% "mutation"
private abbrev state := v17Example% "initial"
private abbrev machine := v17Example% "machine"
private abbrev bases := v17Example% "bases"
private abbrev sourceArrays := v17Example% "sourceArrays"
private abbrev targetWords := v17Example% "targetWords"

theorem compile_identity : Compiler.compile 1 (Frag.init []) program = some result := by
  exact (Option.some_get (by decide +kernel)).symm

theorem selected : result.isMemoryCalls = true := by decide +kernel
theorem expanded_frame : result.requiredFrame = 12 := by decide +kernel
theorem reached_allocation : result.allocationCost state = 5 := by decide +kernel
theorem endpoint_input : result.Input 1 128 bases state machine :=
  Solidity.Evm.Memory.CallExamples.mutation_input
theorem endpoint_agreement : result.Agrees 1 128 bases state machine :=
  Solidity.Evm.Memory.CallExamples.mutation_agrees

theorem private_frame_rejected : ¬ result.Input 1 5 bases state machine :=
  Solidity.Evm.Memory.CallExamples.privateFrame_refused

theorem source_alias_observation : sourceArrays (program.run state) [(0,0),(1,0),(1,1)] =
    some [2,7,88,0] := by decide +kernel

def addresses : List Nat := [0,127,2,program.ext.depth,256,257,258,259,260]
def expected : Option (List Nat) := some [77,261,99,42,8,1,7,2,88,0]
theorem target_observation : targetWords (run result.code machine) addresses = expected := by
  decide +kernel

theorem wrong_code_rejected : targetWords (run [] machine) addresses ≠ expected := by
  decide +kernel
theorem wrong_alias_rejected : sourceArrays (program.run state) [(0,0),(1,0),(1,1)] ≠
    some [2,0,88,0] := by decide +kernel

#eval IO.println ("V17_MEMORY_CALLS_BEGIN\n" ++ (Json.mkObj [
  ("schema", toJson (1 : Nat)), ("isMemoryCalls", toJson result.isMemoryCalls),
  ("usesMemory", toJson result.usesMemory), ("requiredFrame", toJson result.requiredFrame),
  ("callerFrame", toJson (frameNeedProg program)), ("allocationCost", toJson (result.allocationCost state)),
  ("sourceAliases", toJson (sourceArrays (program.run state) [(0,0),(1,0),(1,1)])),
  ("targetWords", toJson (targetWords (run result.code machine) addresses)),
  ("emptyCodeWords", toJson (targetWords (run [] machine) addresses)),
  ("intrinsicCode", toJson (reprStr result.code)),
  ("semanticPremisesDischarged", toJson false), ("releaseClosed", toJson false)]).compress ++
  "\nV17_MEMORY_CALLS_END")

#print axioms compile_identity
#print axioms endpoint_input
#print axioms endpoint_agreement
#print axioms target_observation
#print axioms wrong_code_rejected
#print axioms wrong_alias_rejected
#print axioms private_frame_rejected
end Solidity.Roadmap.V17.MemoryCalls
