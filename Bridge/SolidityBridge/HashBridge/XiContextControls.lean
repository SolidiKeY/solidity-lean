import SolidityBridge.HashBridge.XiContextMessage
import SolidityBridge.ExternalEvm.PaddingInterface

/-! Generalized same-input fuel/error controls. The H7 zero-length law is
consumed as a kernel theorem, never as native allocator/hash correspondence. -/
namespace Solidity.HashBridge.XiContext
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof Solidity.Evm.External

theorem query_empty (i : Inputs) : query i = [] := by
  have zero : (UInt256.ofNat 0).toNat = 0 := rfl
  simp only [query,machineQuery,zero]
  rw [Memory.readWithPadding_zero]
  rfl

theorem before_hash_exhaustion (dest : Array UInt256) (i : Inputs)
    (code : i.environment.code = program) :
    DriverQueryReceipt 3 dest (initial i) [] (.error .OutOfFuel) ∧
      X 3 dest (initial i) = .error .OutOfFuel := by
  have checked : checks dest (ready i) = .ok (hashMemoryCharged (ready i),hashOpcodeCost (ready i)) := by
    rw [hash_checks dest _ (fetches i code).2.2,hash_ready i]
    rfl
  have exhausted : X 1 dest (ready i) = .error .OutOfFuel := evaluator_zero dest _ _ _ checked
  have terminal : DriverQueryReceipt 1 dest (ready i) [] (.error .OutOfFuel) := by
    rw [← exhausted]
    exact driver_one_queries dest _
  have second : DriverQueryReceipt 2 dest (pushed i) [] (.error .OutOfFuel) := by
    have joined : DriverQueryReceipt 2 dest (pushed i)
        (directQueries (fetched (pushed i)).1 (pushed i) ++ []) (.error .OutOfFuel) :=
      query_receipt_prepend 0 2 dest _ _ _ [] _ (push_checks dest i code).2
        (push_steps 0 i code).2 (by rw [(fetches i code).2.1]; rfl) terminal
    simpa only [(fetches i code).2.1,directQueries,Bool.false_eq_true,if_false,List.nil_append] using joined
  have full : DriverQueryReceipt 3 dest (initial i) [] (.error .OutOfFuel) := by
    have joined : DriverQueryReceipt 3 dest (initial i)
        (directQueries (fetched (initial i)).1 (initial i) ++ []) (.error .OutOfFuel) :=
      query_receipt_prepend 1 2 dest _ _ _ [] _ (push_checks dest i code).1
        (push_steps 1 i code).1 (by rw [(fetches i code).1]; rfl) second
    simpa only [(fetches i code).1,directQueries,Bool.false_eq_true,if_false,List.nil_append] using joined
  exact ⟨full,full.sound⟩

theorem zero_gas_order (dest : Array UInt256) (i : Inputs) (code : i.environment.code = program) :
    X 0 dest {initial i with gasAvailable := .ofNat 0} = .error .OutOfFuel ∧
      X 1 dest {initial i with gasAvailable := .ofNat 0} = .error .OutOfGass := by
  refine ⟨rfl,?_⟩
  apply check_failure 0
  have hf : fetched {initial i with gasAvailable := .ofNat 0} = (.Push .PUSH0,none) :=
    (fetches i code).1
  have hm : memoryExpansionCost {initial i with gasAvailable := .ofNat 0} (.Push .PUSH0) = 0 := by
    simp only [memoryExpansionCost,memoryExpansionCost.μᵢ',Nat.sub_self]
  simp only [checks,hf,hm,word_sub_zero]
  rfl

/-- All actual nonempty/empty worlds and distinct snapshots use the same
checked prefix; low fuel has no invented public error state or bytes. -/
theorem public_fuel_boundary (i : Inputs) (code : i.environment.code = program) :
    XiQueryReceipt 4 i.created i.genesis i.blocks i.world i.snapshot (.ofNat 34)
      i.accrued i.environment [] (.error .OutOfFuel) ∧
      Ξ 4 i.created i.genesis i.blocks i.world i.snapshot (.ofNat 34) i.accrued i.environment = .error .OutOfFuel ∧
      Ξ 6 i.created i.genesis i.blocks i.world i.snapshot (.ofNat 34) i.accrued i.environment =
      .ok (.success (i.created,i.world,.ofNat 0,i.accrued) .empty) := by
  have receipt : XiQueryReceipt 4 i.created i.genesis i.blocks i.world i.snapshot (.ofNat 34)
      i.accrued i.environment [] (.error .OutOfFuel) :=
    ⟨.error .OutOfFuel,(before_hash_exhaustion (D_J i.environment.code (.ofNat 0)) i code).1,rfl⟩
  exact ⟨receipt,receipt.sound,(completed_invocation 0 i code).2⟩

end Solidity.HashBridge.XiContext
