import SolidityBridge.RoadmapV15.P10.FrozenWitness

/-! Charged return-byte range checks, consuming the frozen actual fetched API.
No execution/decoder success, padding, allocator or caller-storage frame is an
input oracle. Gas adequacy is stated at both ORIGINAL native charging stages. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Exactly the driver's first gas update; all other fields retain identity. -/
def returnCopyCharged (s : EVM.State) : EVM.State :=
  {s with gasAvailable := s.gasAvailable - .ofNat (EVM.memoryExpansionCost s .RETURNDATACOPY)}

/-- Actual ordered gate, including natural (not modulo-word) source endpoint. -/
theorem return_copy_gate_classification (valid : Array UInt256) (s : EVM.State) :
    Assembly.driverGate valid s .RETURNDATACOPY =
      if s.gasAvailable.toNat < EVM.memoryExpansionCost s .RETURNDATACOPY then
        .error .OutOfGass
      else if (returnCopyCharged s).gasAvailable.toNat < EVM.C' (returnCopyCharged s) .RETURNDATACOPY then
        .error .OutOfGass
      else if s.stack.length < 3 then .error .StackUnderflow
      else if (s.stack.getD 1 ⟨0⟩).toNat + (s.stack.getD 2 ⟨0⟩).toNat > s.returnData.size then
        .error .InvalidMemoryAccess
      else if s.stack.length - 3 > 1024 then .error .StackOverflow
      else .ok (returnCopyCharged s,EVM.C' (returnCopyCharged s) .RETURNDATACOPY) := by
  unfold Assembly.driverGate returnCopyCharged
  simp only [EVM.δ,EVM.α,Option.getD_some,reduceCtorEq,false_and,and_false,true_and,
    List.mem_cons,List.not_mem_nil,false_or,decide_false,Bool.false_eq_true,
    Operation.isCreate,if_false,Nat.add_zero]
  split_ifs <;> simp_all only [bind,Except.bind,pure,Except.pure]

/-- Exact preservation by the gas-only charge, not an execution frame premise. -/
theorem return_copy_charge_frame (s : EVM.State) :
    (returnCopyCharged s).toState = s.toState ∧
    (returnCopyCharged s).activeWords = s.activeWords ∧
    (returnCopyCharged s).memory = s.memory ∧
    (returnCopyCharged s).returnData = s.returnData ∧
    (returnCopyCharged s).H_return = s.H_return ∧
    (returnCopyCharged s).stack = s.stack ∧
    (returnCopyCharged s).pc = s.pc ∧
    (returnCopyCharged s).execLength = s.execLength :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Refusal derives from actual range/charges; even oversized tails cannot move
this source-range check behind capacity/static checks. -/
theorem return_copy_range_refusal (site : Site .RETURNDATACOPY)
    (valid : Array UInt256) (fuel : Nat)
    (firstGas : EVM.memoryExpansionCost site.state .RETURNDATACOPY ≤ site.state.gasAvailable.toNat)
    (secondGas : EVM.C' (returnCopyCharged site.state) .RETURNDATACOPY ≤
      (returnCopyCharged site.state).gasAvailable.toNat)
    (arity : 3 ≤ site.state.stack.length)
    (outside : site.state.returnData.size <
      (site.state.stack.getD 1 ⟨0⟩).toNat + (site.state.stack.getD 2 ⟨0⟩).toNat) :
    Assembly.driverGate valid site.state .RETURNDATACOPY = .error .InvalidMemoryAccess ∧
    Assembly.driverSteps 1 (fuel+2) valid site.state = .error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) valid site.state = .error .InvalidMemoryAccess := by
  have gate : Assembly.driverGate valid site.state .RETURNDATACOPY = .error .InvalidMemoryAccess := by
    rw [return_copy_gate_classification]
    rw [if_neg (Nat.not_lt_of_ge firstGas),if_neg (Nat.not_lt_of_ge secondGas),
      if_neg (Nat.not_lt_of_ge arity),if_pos outside]
  have step : Assembly.driverSteps 1 (fuel+2) valid site.state = .error .InvalidMemoryAccess := by
    rw [FrozenV1.api.charged.checked_return_copy site valid fuel,gate]
  refine ⟨gate,step,?_⟩
  rw [FrozenV1.api.continuation.x_return_copy site valid fuel,step]

/-- An in-range gate produces its exact gas-only charged State. This is not a
physical byte-copy/read-value theorem, even when length is zero. -/
theorem return_copy_range_admitted (valid : Array UInt256) (s : EVM.State)
    (firstGas : EVM.memoryExpansionCost s .RETURNDATACOPY ≤ s.gasAvailable.toNat)
    (secondGas : EVM.C' (returnCopyCharged s) .RETURNDATACOPY ≤ (returnCopyCharged s).gasAvailable.toNat)
    (arity : 3 ≤ s.stack.length)
    (inside : (s.stack.getD 1 ⟨0⟩).toNat + (s.stack.getD 2 ⟨0⟩).toNat ≤ s.returnData.size)
    (capacity : s.stack.length-3 ≤ 1024) :
    Assembly.driverGate valid s .RETURNDATACOPY =
      .ok (returnCopyCharged s,EVM.C' (returnCopyCharged s) .RETURNDATACOPY) := by
  rw [return_copy_gate_classification]
  rw [if_neg (Nat.not_lt_of_ge firstGas),if_neg (Nat.not_lt_of_ge secondGas),
    if_neg (Nat.not_lt_of_ge arity),if_neg (Nat.not_lt_of_ge inside),if_neg (Nat.not_lt_of_ge capacity)]

#print axioms return_copy_gate_classification
#print axioms return_copy_charge_frame
#print axioms return_copy_range_refusal
#print axioms return_copy_range_admitted
end SolidityBridge.RoadmapV15.P10
