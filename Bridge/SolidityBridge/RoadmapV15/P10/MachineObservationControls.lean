import SolidityBridge.RoadmapV15.P10.MachineObservation
namespace SolidityBridge.RoadmapV15.P10.MachineObservationControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def spill : List UInt256 := [u 258,u 513]
private def seed (gas active : Nat) (tail : List UInt256) : EVM.State :=
  {(default : EVM.State) with
    gasAvailable := u gas,activeWords := u active,execLength := 41,stack := tail
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := false
      calldata := ⟨#[0x11,0x22,0x33]⟩}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
private def site (op : Backend.Op) (gas active : Nat) (tail : List UInt256 := spill) : Site op :=
  ⟨seed gas active tail,[.push ⟨1,by decide⟩ #v[0x58],.op .POP],[.op .STOP],by decide⟩
private def expected {op : Backend.Op} (input : Site op) (value : UInt256) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 7,execLength := 42
    stack := value::input.state.stack}

private theorem normalize (s : EVM.State) (value : UInt256)
    (pc : s.pc = u 3) (gas : s.gasAvailable = u 9) (count : s.execLength = 41) :
    (Assembly.chargedPrepare s 2).replaceStackAndIncrPC (value::s.stack) =
      {s with pc := u 4,gasAvailable := u 7,execLength := 42,stack := value::s.stack} := by
  change {s with
    pc := s.pc+u 1
    gasAvailable := s.gasAvailable-u 2
    execLength := s.execLength+1
    stack := value::s.stack} = _
  rw [pc,gas,count]
  rw [show u 3+u 1=u 4 from by decide +kernel,show u 9-u 2=u 7 from by decide +kernel]

theorem pc_populated : Assembly.driverSteps 1 2 #[] (site .PC 9 3).state =
    .ok (expected (site .PC 9 3) (u 3)) := by
  have h := (pc_agreement (site .PC 9 3) 0 (by decide +kernel) (by decide +kernel)).1
  rw [normalize _ _ rfl rfl rfl] at h
  exact h

theorem gas_populated : Assembly.driverSteps 1 2 #[] (site .GAS 9 3).state =
    .ok (expected (site .GAS 9 3) (u 7)) := by
  have h := (gas_agreement (site .GAS 9 3) 0 (by decide +kernel) (by decide +kernel)).1
  rw [normalize _ _ rfl rfl rfl] at h
  have gas : (Assembly.chargedPrepare (site .GAS 9 3).state 2).gasAvailable = u 7 := by
    change u 9-u 2=u 7
    decide +kernel
  rw [gas] at h
  exact h

theorem msize_populated : Assembly.driverSteps 1 2 #[] (site .MSIZE 9 3).state =
    .ok (expected (site .MSIZE 9 3) (u 96)) := by
  have h := (msize_agreement (site .MSIZE 9 3) 0 (by decide +kernel) (by decide +kernel)).1
  rw [normalize _ _ rfl rfl rfl] at h
  have size : (site .MSIZE 9 3).state.activeWords*UInt256.ofNat 32=u 96 := by decide +kernel
  rw [size] at h
  exact h

theorem ordered_code : (site .PC 9 3).state.executionEnv.code.data.toList =
    [0x60,0x58,0x50,0x58,0x00] := rfl

theorem pc_not_incremented : Assembly.driverSteps 1 2 #[] (site .PC 9 3).state ≠
    .ok (expected (site .PC 9 3) (u 4)) := by
  rw [pc_populated]
  intro h
  have stack := congrArg (fun o => o.toOption.map (·.stack)) h
  have first := congrArg (fun o => o.map (·.head?)) stack
  change some (some (u 3)) = some (some (u 4)) at first
  have different : u 3 ≠ u 4 := by decide +kernel
  exact different (Option.some.inj (Option.some.inj first))

theorem gas_not_initial : Assembly.driverSteps 1 2 #[] (site .GAS 9 3).state ≠
    .ok (expected (site .GAS 9 3) (u 9)) := by
  rw [gas_populated]
  intro h
  have stack := congrArg (fun o => o.toOption.map (·.stack.head?)) h
  change some (some (u 7)) = some (some (u 9)) at stack
  exact (by decide +kernel : u 7 ≠ u 9) (Option.some.inj (Option.some.inj stack))

theorem memory_size_is_not_resident_length :
    (site .MSIZE 9 3).state.memory.size = 2 ∧ (site .MSIZE 9 3).state.activeWords*u 32 ≠ u 2 := by
  decide +kernel

theorem zero_active : Assembly.driverSteps 1 2 #[] (site .MSIZE 9 0).state =
    .ok (expected (site .MSIZE 9 0) (u 0)) := by
  have h := (msize_agreement (site .MSIZE 9 0) 0 (by decide +kernel) (by decide +kernel)).1
  rw [normalize _ _ rfl rfl rfl] at h
  exact h

/-- A raw native-word boundary, not a physical allocator adequacy witness. -/
theorem maximum_active_wrap : Assembly.driverSteps 1 2 #[] (site .MSIZE 9 (2^256-1)).state =
    .ok (expected (site .MSIZE 9 (2^256-1)) (u (2^256-32))) := by
  have h := (msize_agreement (site .MSIZE 9 (2^256-1)) 0 (by decide +kernel) (by decide +kernel)).1
  rw [normalize _ _ rfl rfl rfl] at h
  have size : (site .MSIZE 9 (2^256-1)).state.activeWords*UInt256.ofNat 32=u (2^256-32) := by decide +kernel
  rw [size] at h
  exact h

theorem stack_boundary : Assembly.driverSteps 1 2 #[]
    (site .PC 9 3 (List.replicate 1023 (u 513))).state =
    .ok (expected (site .PC 9 3 (List.replicate 1023 (u 513))) (u 3)) := by
  have room : (site .PC 9 3 (List.replicate 1023 (u 513))).state.stack.length+1≤1024 := by
    change (List.replicate 1023 (u 513)).length+1≤1024
    rw [List.length_replicate]
  have h := (pc_agreement _ 0 (by decide +kernel) room).1
  rw [normalize _ _ rfl rfl rfl] at h
  exact h

theorem gas_refusal : Assembly.driverSteps 1 2 #[] (site .GAS 1 3).state = .error .OutOfGass := by
  rfl

private theorem capacity_error (tail : List UInt256) (big : 1024 ≤ tail.length) :
    Assembly.driverSteps 1 2 #[] (site .PC 9 3 tail).state = .error .StackOverflow := by
  let input := (site .PC 9 3 tail).state
  have expansion : EVM.memoryExpansionCost input .PC = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : input.gasAvailable-UInt256.ofNat 0=input.gasAvailable := by
    change UInt256.mk (input.gasAvailable.val-0)=input.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' input .PC=2 := rfl
  have gas : ¬input.gasAvailable.toNat < 2 := by change ¬(u 9).toNat < 2;decide +kernel
  have capacity : input.stack.length+1 > 1024 := by change tail.length+1>1024;omega
  have gate : Assembly.driverGate #[] input .PC = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,reduceCtorEq,false_and,if_false,
      Nat.sub_zero,if_neg (Nat.not_lt_zero _),if_neg gas,if_pos capacity]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc=some (.PC,none) := DecoderAgreement.decode_all _
  change Assembly.driverSteps 1 2 #[] input = _
  simp only [Assembly.driverSteps]
  rw [decoded]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]

theorem capacity_refusal : Assembly.driverSteps 1 2 #[]
    (site .PC 9 3 (List.replicate 1024 (u 513))).state = .error .StackOverflow := by
  apply capacity_error
  rw [List.length_replicate]

theorem fuel_refusal : Assembly.driverSteps 1 1 #[] (site .PC 0 3).state = .error .OutOfFuel := rfl

private def image : ByteArray := ⟨#[0x60,0x58,0x50,0x58,0x5a,0x59,0x00]⟩
private def sequenceState (gas pc count : Nat) (words : List UInt256) : EVM.State :=
  {seed gas 3 words with
    pc := u pc,execLength := count
    executionEnv := {(seed gas 3 words).executionEnv with code := image}}
private def sequencePC : Site .PC :=
  ⟨seed 9 3 spill,[.push ⟨1,by decide⟩ #v[0x58],.op .POP],
    [.op .GAS,.op .MSIZE,.op .STOP],by decide⟩
private def sequenceGas : Site .GAS :=
  ⟨{seed 7 3 (u 3::spill) with execLength := 42},
    [.push ⟨1,by decide⟩ #v[0x58],.op .POP,.op .PC],[.op .MSIZE,.op .STOP],by decide⟩
private def sequenceMsize : Site .MSIZE :=
  ⟨{seed 5 3 (u 5::u 3::spill) with execLength := 43},
    [.push ⟨1,by decide⟩ #v[0x58],.op .POP,.op .PC,.op .GAS],[.op .STOP],by decide⟩

private theorem first_step : Assembly.driverSteps 1 4 #[] (sequenceState 9 3 41 spill) =
    .ok (sequenceState 7 4 42 (u 3::spill)) := by
  have h := (pc_agreement sequencePC 2 (by decide +kernel) (by decide +kernel)).1
  change Assembly.driverSteps 1 4 #[] (sequenceState 9 3 41 spill) =
    .ok {sequenceState 9 3 41 spill with
      gasAvailable := u 9-u 2,pc := u 3+u 1,execLength := 42,stack := u 3::spill} at h
  rw [show u 9-u 2=u 7 from by decide +kernel,show u 3+u 1=u 4 from by decide +kernel] at h
  exact h

private theorem second_step : Assembly.driverSteps 1 3 #[] (sequenceState 7 4 42 (u 3::spill)) =
    .ok (sequenceState 5 5 43 (u 5::u 3::spill)) := by
  have h := (gas_agreement sequenceGas 1 (by decide +kernel) (by decide +kernel)).1
  change Assembly.driverSteps 1 3 #[] (sequenceState 7 4 42 (u 3::spill)) =
    .ok {sequenceState 7 4 42 (u 3::spill) with
      gasAvailable := u 7-u 2,pc := u 4+u 1,execLength := 43,stack := (u 7-u 2)::u 3::spill} at h
  rw [show u 7-u 2=u 5 from by decide +kernel,show u 4+u 1=u 5 from by decide +kernel] at h
  exact h

private theorem third_step : Assembly.driverSteps 1 2 #[] (sequenceState 5 5 43 (u 5::u 3::spill)) =
    .ok (sequenceState 3 6 44 (u 96::u 5::u 3::spill)) := by
  have h := (msize_agreement sequenceMsize 0 (by decide +kernel) (by decide +kernel)).1
  change Assembly.driverSteps 1 2 #[] (sequenceState 5 5 43 (u 5::u 3::spill)) =
    .ok {sequenceState 5 5 43 (u 5::u 3::spill) with
      gasAvailable := u 5-u 2,pc := u 5+u 1,execLength := 44,stack := (u 3*u 32)::u 5::u 3::spill} at h
  rw [show u 5-u 2=u 3 from by decide +kernel,show u 5+u 1=u 6 from by decide +kernel,
    show u 3*u 32=u 96 from by decide +kernel] at h
  exact h

theorem fetched_combination : Assembly.driverSteps 3 4 #[] (sequenceState 9 3 41 spill) =
    .ok (sequenceState 3 6 44 [u 96,u 5,u 3,u 258,u 513]) := by
  rw [fetched_steps_cons 2 2,first_step]
  dsimp only [Except.bind]
  rw [fetched_steps_cons 1 1,second_step]
  dsimp only [Except.bind]
  exact third_step

theorem combination_ordered_code : (sequenceState 9 3 41 spill).executionEnv.code.data.toList =
    [0x60,0x58,0x50,0x58,0x5a,0x59,0x00] := rfl


#print axioms pc_populated
#print axioms gas_populated
#print axioms msize_populated
#print axioms ordered_code
#print axioms pc_not_incremented
#print axioms gas_not_initial
#print axioms memory_size_is_not_resident_length
#print axioms zero_active
#print axioms maximum_active_wrap
#print axioms stack_boundary
#print axioms gas_refusal
#print axioms capacity_refusal
#print axioms fuel_refusal
#print axioms fetched_combination
#print axioms combination_ordered_code
end SolidityBridge.RoadmapV15.P10.MachineObservationControls
