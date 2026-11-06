import SolidityBridge.RoadmapV15.P10.StorageChaseExecution

/-! Exact second-charge observation at the actual first-loaded value.
The equal-key and distinct-key cases exhaust every numeric value; no alias premise
is silently assumed and no symbolic/hash injectivity is introduced. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem storage_chase_second_charge (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256) :
    EVM.C' (storageChaseFirst seed before after key tail) .SLOAD =
      if storageChaseValue seed before after key tail = key then 100
      else EVM.C' {(storageChaseInput seed before after key tail) with
        stack := storageChaseValue seed before after key tail::tail} .SLOAD := by
  let input := storageChaseInput seed before after key tail
  let first := storageChaseFirst seed before after key tail
  let value := storageChaseValue seed before after key tail
  by_cases same : value = key
  · simp only [show storageChaseValue seed before after key tail = key from same,if_pos]
    have warm := sload_warm_cost input key tail (EVM.C' input .SLOAD)
    change EVM.C' {first with stack := key::tail} .SLOAD = 100 at warm
    change EVM.C' {first with stack := value::tail} .SLOAD = 100
    rw [same]
    exact warm
  · simp only [show ¬storageChaseValue seed before after key tail = key from same,if_neg]
    have apart : (input.executionEnv.codeOwner,value) ≠ (input.executionEnv.codeOwner,key) := by
      intro h
      exact same (congrArg Prod.snd h)
    have other := sload_distinct_cost input key value input.executionEnv.codeOwner tail (EVM.C' input .SLOAD) apart
    simpa only [input,first,value,storageChaseFirst,storageChaseInput,storageChaseValue,
      EvmYul.State.sload,EvmYul.State.addAccessedStorageKey,Assembly.chargedPrepare,
      EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using other

#print axioms storage_chase_second_charge
end SolidityBridge.RoadmapV15.P10
