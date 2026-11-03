import SolidityBridge.RoadmapV15.P10.StorageChaseLayout
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Two actual fetched SLOADs: the second consumes the first loaded value.
The resource premise is exactly the computed two charges, not a desired run. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem storage_chase_execution (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256)
    (fits : (Backend.encode (before ++ [.op .SLOAD])).length < UInt256.size)
    (room : tail.length+1 ≤ 1024)
    (gas : storageChaseCharge seed before after key tail ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 2 (fuel+3) #[] (storageChaseInput seed before after key tail) =
      .ok (storageChaseOutput seed before after key tail) ∧
    EVM.X (fuel+3) #[] (storageChaseInput seed before after key tail) =
      EVM.X (fuel+1) #[] (storageChaseOutput seed before after key tail) := by
  let input := storageChaseInput seed before after key tail
  let first := storageChaseFirst seed before after key tail
  have budget : EVM.C' input .SLOAD + EVM.C' first .SLOAD ≤ seed.gasAvailable.toNat := gas
  have initialFits : (Backend.encode before).length < UInt256.size := by
    rw [storage_chase_prefix_length] at fits
    omega
  have enoughFirst : EVM.C' input .SLOAD ≤ seed.gasAvailable.toNat := by omega
  let firstSite : Site .SLOAD := ⟨seed,before,.op .SLOAD::after,initialFits⟩
  have step1 := sload_agreement firstSite key tail room enoughFirst (fuel+1)
  have firstDriver : Assembly.driverSteps 1 (fuel+3) #[] input = .ok first := by
    simpa only [input,first,firstSite,slotReadSite,Site.state,storageChaseInput,storageChaseCode,
      storageChaseFirst,List.append_assoc,List.cons_append,List.nil_append] using step1.1
  have firstX : EVM.X (fuel+3) #[] input = EVM.X (fuel+2) #[] first := by
    simpa only [input,first,firstSite,slotReadSite,Site.state,storageChaseInput,storageChaseCode,
      storageChaseFirst,List.append_assoc,List.cons_append,List.nil_append] using step1.2
  have enoughSecond : EVM.C' first .SLOAD ≤ first.gasAvailable.toNat := by
    change EVM.C' first .SLOAD ≤ (seed.gasAvailable-UInt256.ofNat (EVM.C' input .SLOAD)).toNat
    rw [reference_gas_debit seed.gasAvailable (EVM.C' input .SLOAD) enoughFirst]
    omega
  have step2 := sload_agreement (storageChaseTailSite first before after fits)
    (storageChaseValue seed before after key tail) tail room enoughSecond fuel
  dsimp only at step2
  rw [storage_chase_tail_alignment] at step2
  constructor
  · rw [fetched_steps_cons 1 (fuel+1),firstDriver]
    exact step2.1
  · exact firstX.trans step2.2

theorem storage_chase_uniform_budget (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256)
    (fits : (Backend.encode (before ++ [.op .SLOAD])).length < UInt256.size)
    (room : tail.length+1 ≤ 1024) (gas : 4200 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 2 (fuel+3) #[] (storageChaseInput seed before after key tail) =
      .ok (storageChaseOutput seed before after key tail) ∧
    EVM.X (fuel+3) #[] (storageChaseInput seed before after key tail) =
      EVM.X (fuel+1) #[] (storageChaseOutput seed before after key tail) := by
  apply storage_chase_execution seed before after key tail fits room _ fuel
  have bounds := storage_chase_cost_bounds seed before after key tail
  dsimp only [storageChaseCharge]
  omega

theorem storage_chase_exact_debit (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256)
    (gas : storageChaseCharge seed before after key tail ≤ seed.gasAvailable.toNat) :
    (storageChaseOutput seed before after key tail).gasAvailable.toNat =
      seed.gasAvailable.toNat-storageChaseCharge seed before after key tail := by
  let input := storageChaseInput seed before after key tail
  let first := storageChaseFirst seed before after key tail
  have budget : EVM.C' input .SLOAD + EVM.C' first .SLOAD ≤ seed.gasAvailable.toNat := gas
  have enoughFirst : EVM.C' input .SLOAD ≤ seed.gasAvailable.toNat := by omega
  have firstGas : first.gasAvailable.toNat = seed.gasAvailable.toNat-EVM.C' input .SLOAD := by
    change (seed.gasAvailable-UInt256.ofNat (EVM.C' input .SLOAD)).toNat = _
    exact reference_gas_debit _ _ enoughFirst
  have enoughSecond : EVM.C' first .SLOAD ≤ first.gasAvailable.toNat := by rw [firstGas];omega
  change (first.gasAvailable-UInt256.ofNat (EVM.C' first .SLOAD)).toNat = _
  rw [reference_gas_debit _ _ enoughSecond,firstGas]
  change seed.gasAvailable.toNat - EVM.C' input .SLOAD - EVM.C' first .SLOAD =
    seed.gasAvailable.toNat - (EVM.C' input .SLOAD + EVM.C' first .SLOAD)
  simp only [Nat.sub_sub]

theorem storage_chase_storage_frame (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256) :
    Solidity.Evm.StorageSlots.storageRead (storageChaseOutput seed before after key tail).toState =
      Solidity.Evm.StorageSlots.storageRead (storageChaseInput seed before after key tail).toState := by
  let input := storageChaseInput seed before after key tail
  let first := storageChaseFirst seed before after key tail
  have a := Solidity.Evm.StorageSlots.sload_preserves input.toState key
  have b := Solidity.Evm.StorageSlots.sload_preserves first.toState (storageChaseValue seed before after key tail)
  exact b.trans a

theorem storage_chase_transient_frame (seed : EVM.State) (before after : Backend.Program)
    (key probe : UInt256) (tail : List UInt256) :
    (EvmYul.State.tload (storageChaseOutput seed before after key tail).toState probe).2 =
      (EvmYul.State.tload (storageChaseInput seed before after key tail).toState probe).2 := by rfl

#print axioms storage_chase_execution
#print axioms storage_chase_uniform_budget
#print axioms storage_chase_exact_debit
#print axioms storage_chase_storage_frame
#print axioms storage_chase_transient_frame
end SolidityBridge.RoadmapV15.P10
