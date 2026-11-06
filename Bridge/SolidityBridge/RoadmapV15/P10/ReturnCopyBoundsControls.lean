import SolidityBridge.RoadmapV15.P10.ReturnCopyBounds
namespace SolidityBridge.RoadmapV15.P10.ReturnCopyBoundsControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def seed (gas : Nat) (args : List UInt256) (perm : Bool) : EVM.State :=
  {(default : EVM.State) with
    gasAvailable := .ofNat gas,activeWords := .ofNat 1,execLength := 41,stack := args
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0x11,0x22,0x33]⟩,H_return := ⟨#[0xee,0xff]⟩
    accountMap := ((default : EVM.State).accountMap.insert (.ofNat 7)
      {(default : Account .EVM) with nonce := .ofNat 3,balance := .ofNat 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := .ofNat 5,balance := .ofNat 41}
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,perm := perm
      calldata := ⟨#[0x44,0x55,0x66]⟩}}
private def site (gas : Nat) (args : List UInt256) (perm : Bool := false) : Site .RETURNDATACOPY :=
  ⟨seed gas args perm,[.push ⟨1,by decide⟩ #v[0x3e],.op .POP],[.op .STOP],by decide⟩
private def words (destination source length : Nat) (tail : List UInt256 := [.ofNat 258,.ofNat 513]) :=
  UInt256.ofNat destination :: UInt256.ofNat source :: UInt256.ofNat length :: tail

private theorem expansion_shape (gas destination source length : Nat) (tail : List UInt256) (perm : Bool) :
    EVM.memoryExpansionCost (site gas (words destination source length tail) perm).state .RETURNDATACOPY =
      EVM.Cₘ (.ofNat (MachineState.M (UInt256.ofNat 1).toNat (UInt256.ofNat destination).toNat
        (UInt256.ofNat length).toNat)) - EVM.Cₘ (.ofNat 1) := rfl

private theorem copy_cost_shape (gas destination source length : Nat) (tail : List UInt256) (perm : Bool) :
    EVM.C' (returnCopyCharged (site gas (words destination source length tail) perm).state) .RETURNDATACOPY =
      3+3*(((UInt256.ofNat length).toNat+31)/32) := by
  simp only [EVM.C']
  rw [if_pos (by decide : Operation.RETURNDATACOPY ∈ EVM.InstructionGasGroups.Wcopy)]
  rfl

private theorem from_gate (s : Site .RETURNDATACOPY) (fuel : Nat) (error : EVM.ExecutionException)
    (gate : Assembly.driverGate #[] s.state .RETURNDATACOPY = .error error) :
    Assembly.driverSteps 1 (fuel+2) #[] s.state = .error error ∧
    EVM.X (fuel+2) #[] s.state = .error error := by
  have step : Assembly.driverSteps 1 (fuel+2) #[] s.state = .error error := by
    rw [FrozenV1.api.charged.checked_return_copy s #[] fuel,gate]
  refine ⟨step,?_⟩
  rw [FrozenV1.api.continuation.x_return_copy s #[] fuel,step]

theorem ordered_code : (site 6 (words 5 2 2)).state.executionEnv.code.data.toList =
    [0x60,0x3e,0x50,0x3e,0x00] := rfl

theorem populated_refusal (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 6 (words 5 2 2)).state = .error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) #[] (site 6 (words 5 2 2)).state = .error .InvalidMemoryAccess := by
  exact (return_copy_range_refusal (site 6 (words 5 2 2)) #[] fuel
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

theorem expansion_gas_first (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 2 (words 32 3 1)).state = .error .OutOfGass ∧
    EVM.X (fuel+2) #[] (site 2 (words 32 3 1)).state = .error .OutOfGass := by
  apply from_gate
  rw [return_copy_gate_classification,if_pos (by decide +kernel :
    (site 2 (words 32 3 1)).state.gasAvailable.toNat <
      EVM.memoryExpansionCost (site 2 (words 32 3 1)).state .RETURNDATACOPY)]

theorem second_gas_before_range (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 8 (words 32 3 1)).state = .error .OutOfGass ∧
    EVM.X (fuel+2) #[] (site 8 (words 32 3 1)).state = .error .OutOfGass := by
  apply from_gate
  rw [return_copy_gate_classification,
    if_neg (by decide +kernel : ¬(site 8 (words 32 3 1)).state.gasAvailable.toNat <
      EVM.memoryExpansionCost (site 8 (words 32 3 1)).state .RETURNDATACOPY),
    if_pos (by decide +kernel : (returnCopyCharged (site 8 (words 32 3 1)).state).gasAvailable.toNat <
      EVM.C' (returnCopyCharged (site 8 (words 32 3 1)).state) .RETURNDATACOPY)]

theorem expansion_paid_range_refuses (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 9 (words 32 3 1)).state = .error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) #[] (site 9 (words 32 3 1)).state = .error .InvalidMemoryAccess := by
  exact (return_copy_range_refusal (site 9 (words 32 3 1)) #[] fuel
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

theorem arity_before_range (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 3 [.ofNat 5,.ofNat 4]).state = .error .StackUnderflow ∧
    EVM.X (fuel+2) #[] (site 3 [.ofNat 5,.ofNat 4]).state = .error .StackUnderflow := by
  apply from_gate
  rw [return_copy_gate_classification,
    if_neg (by decide +kernel : ¬(site 3 [.ofNat 5,.ofNat 4]).state.gasAvailable.toNat <
      EVM.memoryExpansionCost (site 3 [.ofNat 5,.ofNat 4]).state .RETURNDATACOPY),
    if_neg (by decide +kernel : ¬(returnCopyCharged (site 3 [.ofNat 5,.ofNat 4]).state).gasAvailable.toNat <
      EVM.C' (returnCopyCharged (site 3 [.ofNat 5,.ofNat 4]).state) .RETURNDATACOPY),
    if_pos (by decide +kernel : (site 3 [.ofNat 5,.ofNat 4]).state.stack.length < 3)]

theorem exact_end_gate (perm : Bool) :
    Assembly.driverGate #[] (site 6 (words 5 1 2) perm).state .RETURNDATACOPY =
      .ok (returnCopyCharged (site 6 (words 5 1 2) perm).state,6) := by
  have h := return_copy_range_admitted #[] (site 6 (words 5 1 2) perm).state
    (by rw [expansion_shape]; change _ ≤ (UInt256.ofNat 6).toNat; decide +kernel)
    (by rw [copy_cost_shape]; change _ ≤ (UInt256.ofNat 6 - .ofNat
      (EVM.memoryExpansionCost _ .RETURNDATACOPY)).toNat
        rw [expansion_shape]; decide +kernel)
    (by change 3 ≤ 5; decide)
    (by change 1+2 ≤ 3; decide) (by change 5-3 ≤ 1024; decide)
  rw [copy_cost_shape] at h
  exact h

theorem zero_at_end_gate :
    Assembly.driverGate #[] (site 3 (words (2^256-1) 3 0)).state .RETURNDATACOPY =
      .ok (returnCopyCharged (site 3 (words (2^256-1) 3 0)).state,3) := by
  exact return_copy_range_admitted #[] _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem zero_beyond_end_refuses (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 3 (words 5 4 0)).state = .error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) #[] (site 3 (words 5 4 0)).state = .error .InvalidMemoryAccess := by
  exact (return_copy_range_refusal (site 3 (words 5 4 0)) #[] fuel
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

theorem endpoint_no_word_wrap (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 6 (words 5 (2^256-1) 1)).state = .error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) #[] (site 6 (words 5 (2^256-1) 1)).state = .error .InvalidMemoryAccess := by
  exact (return_copy_range_refusal (site 6 (words 5 (2^256-1) 1)) #[] fuel
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

theorem range_before_capacity (tail : List UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 6 (words 5 2 2 tail)).state = .error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) #[] (site 6 (words 5 2 2 tail)).state = .error .InvalidMemoryAccess := by
  apply (return_copy_range_refusal (site 6 (words 5 2 2 tail)) #[] fuel
    (by rw [expansion_shape]; change _ ≤ (UInt256.ofNat 6).toNat; decide +kernel)
    (by rw [copy_cost_shape]; change _ ≤ (UInt256.ofNat 6 - .ofNat
      (EVM.memoryExpansionCost _ .RETURNDATACOPY)).toNat
        rw [expansion_shape]; decide +kernel)
    ?_ (by change 3 < 2+2; decide)).2
  change 3 ≤ (words 5 2 2 tail).length
  simp only [words,List.length_cons]
  omega

theorem populated_overflow_witness (fuel : Nat) :
    ∃ tail : List UInt256, tail.length = 1025 ∧
      Assembly.driverSteps 1 (fuel+2) #[] (site 6 (words 5 2 2 tail)).state = .error .InvalidMemoryAccess := by
  refine ⟨List.replicate 1025 (.ofNat 513),List.length_replicate,?_⟩
  exact (range_before_capacity _ fuel).1

theorem zero_fuel_precedes_gate :
    Assembly.driverSteps 1 1 #[] (site 0 (words 5 2 2)).state = .error .OutOfFuel := rfl

theorem range_refusal_no_success (fuel : Nat) (next : EVM.State) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 6 (words 5 2 2)).state ≠ .ok next := by
  rw [(populated_refusal fuel).1]
  intro h
  cases h

theorem return_buffer_not_halt_buffer :
    (site 6 (words 5 1 2)).state.returnData.data.toList = [0x11,0x22,0x33] ∧
    (site 6 (words 5 1 2)).state.H_return.data.toList = [0xee,0xff] ∧
    3 > (site 6 (words 5 1 2)).state.H_return.size := by decide +kernel

theorem charged_entire_state :
    returnCopyCharged (site 9 (words 32 2 1)).state =
      {(site 9 (words 32 2 1)).state with gasAvailable := .ofNat 6} := by
  have expansion : EVM.memoryExpansionCost (site 9 (words 32 2 1)).state .RETURNDATACOPY = 3 := by
    rw [expansion_shape]
    decide +kernel
  unfold returnCopyCharged
  rw [expansion]
  rw [show (site 9 (words 32 2 1)).state.gasAvailable = UInt256.ofNat 9 from rfl]
  rw [show UInt256.ofNat 9 - UInt256.ofNat 3 = UInt256.ofNat 6 from by decide +kernel]

theorem populated_observations :
    (site 6 (words 5 2 2)).state.stack = [.ofNat 5,.ofNat 2,.ofNat 2,.ofNat 258,.ofNat 513] ∧
    (site 6 (words 5 2 2)).state.memory.data.toList = [0xaa,0xbb] ∧
    (site 6 (words 5 2 2)).state.returnData.data.toList = [0x11,0x22,0x33] ∧
    (site 6 (words 5 2 2)).state.H_return.data.toList = [0xee,0xff] ∧
    (site 6 (words 5 2 2)).state.executionEnv.calldata.data.toList = [0x44,0x55,0x66] ∧
    (site 6 (words 5 2 2)).state.executionEnv.codeOwner = .ofNat 7 ∧
    (site 6 (words 5 2 2)).state.executionEnv.source = .ofNat 11 ∧
    (site 6 (words 5 2 2)).state.activeWords = .ofNat 1 ∧
    (site 6 (words 5 2 2)).state.execLength = 41 ∧
    ((site 6 (words 5 2 2)).state.accountMap.find? (.ofNat 7)).map (·.balance) = some (.ofNat 29) ∧
    ((site 6 (words 5 2 2)).state.accountMap.find? (.ofNat 11)).map (·.balance) = some (.ofNat 41) := by
  decide +kernel

theorem in_range_capacity_refuses (tail : List UInt256) (long : 1024 < tail.length) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 6 (words 5 1 2 tail)).state = .error .StackOverflow ∧
    EVM.X (fuel+2) #[] (site 6 (words 5 1 2 tail)).state = .error .StackOverflow := by
  apply from_gate
  have first : ¬(site 6 (words 5 1 2 tail)).state.gasAvailable.toNat <
      EVM.memoryExpansionCost (site 6 (words 5 1 2 tail)).state .RETURNDATACOPY := by
    rw [expansion_shape]
    change ¬(UInt256.ofNat 6).toNat < _
    decide +kernel
  have second : ¬(returnCopyCharged (site 6 (words 5 1 2 tail)).state).gasAvailable.toNat <
      EVM.C' (returnCopyCharged (site 6 (words 5 1 2 tail)).state) .RETURNDATACOPY := by
    rw [copy_cost_shape]
    change ¬(UInt256.ofNat 6 - .ofNat (EVM.memoryExpansionCost _ .RETURNDATACOPY)).toNat < _
    rw [expansion_shape]
    decide +kernel
  have arity : ¬(site 6 (words 5 1 2 tail)).state.stack.length < 3 := by
    change ¬(words 5 1 2 tail).length < 3
    simp only [words,List.length_cons]
    omega
  have inside : ¬(site 6 (words 5 1 2 tail)).state.returnData.size <
      ((site 6 (words 5 1 2 tail)).state.stack.getD 1 ⟨0⟩).toNat +
      ((site 6 (words 5 1 2 tail)).state.stack.getD 2 ⟨0⟩).toNat := by
    change ¬3 < (UInt256.ofNat 1).toNat + (UInt256.ofNat 2).toNat
    decide +kernel
  have capacity : (site 6 (words 5 1 2 tail)).state.stack.length-3 > 1024 := by
    change (words 5 1 2 tail).length-3 > 1024
    simp only [words,List.length_cons]
    omega
  rw [return_copy_gate_classification,if_neg first,if_neg second,if_neg arity,if_neg inside,if_pos capacity]


#print axioms ordered_code
#print axioms populated_refusal
#print axioms expansion_gas_first
#print axioms second_gas_before_range
#print axioms expansion_paid_range_refuses
#print axioms arity_before_range
#print axioms exact_end_gate
#print axioms zero_at_end_gate
#print axioms zero_beyond_end_refuses
#print axioms endpoint_no_word_wrap
#print axioms range_before_capacity
#print axioms populated_overflow_witness
#print axioms zero_fuel_precedes_gate
#print axioms range_refusal_no_success
#print axioms return_buffer_not_halt_buffer
#print axioms charged_entire_state
#print axioms populated_observations
#print axioms in_range_capacity_refuses
end SolidityBridge.RoadmapV15.P10.ReturnCopyBoundsControls
