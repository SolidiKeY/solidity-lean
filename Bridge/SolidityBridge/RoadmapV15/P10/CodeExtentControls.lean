import SolidityBridge.RoadmapV15.P10.CodeExtent
namespace SolidityBridge.RoadmapV15.P10.CodeExtentControls
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

theorem populated : Assembly.driverSteps 1 2 #[] (site .CODESIZE 9 3).state =
    .ok (expected (site .CODESIZE 9 3) (u 5)) := by
  have h := (codesize_agreement (site .CODESIZE 9 3) 0 (by decide +kernel) (by decide +kernel)).1
  rw [normalize _ _ rfl rfl rfl] at h
  exact h

theorem ordered_code : (site .CODESIZE 9 3).state.executionEnv.code.data.toList =
    [0x60,0x58,0x50,0x38,0x00] := rfl

theorem not_pc_or_remaining_extent : Assembly.driverSteps 1 2 #[] (site .CODESIZE 9 3).state ≠
    .ok (expected (site .CODESIZE 9 3) (u 2)) := by
  rw [populated]
  intro h
  have top := congrArg (fun o => o.toOption.map (·.stack.head?)) h
  change some (some (u 5)) = some (some (u 2)) at top
  exact (by decide +kernel : u 5 ≠ u 2) (Option.some.inj (Option.some.inj top))

private def withSuffix : Site .CODESIZE :=
  ⟨seed 9 3 spill,[.push ⟨1,by decide⟩ #v[0x58],.op .POP],
    [.op .STOP,.op .INVALID,.op .JUMPDEST],by decide⟩

theorem suffix_included : Assembly.driverSteps 1 2 #[] withSuffix.state =
    .ok (expected withSuffix (u 7)) := by
  have h := (codesize_agreement withSuffix 0 (by decide +kernel) (by decide +kernel)).1
  rw [normalize _ _ rfl rfl rfl] at h
  exact h

theorem suffix_order : withSuffix.state.executionEnv.code.data.toList =
    [0x60,0x58,0x50,0x38,0x00,0xfe,0x5b] := rfl

theorem gas_refusal : Assembly.driverSteps 1 2 #[] (site .CODESIZE 1 3).state =
    .error .OutOfGass := rfl

theorem fuel_precedes_gas : Assembly.driverSteps 1 1 #[] (site .CODESIZE 0 3).state =
    .error .OutOfFuel := rfl

private theorem capacity_error (tail : List UInt256) (big : 1024 ≤ tail.length) :
    Assembly.driverSteps 1 2 #[] (site .CODESIZE 9 3 tail).state = .error .StackOverflow := by
  let input := (site .CODESIZE 9 3 tail).state
  have expansion : EVM.memoryExpansionCost input .CODESIZE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : input.gasAvailable-UInt256.ofNat 0=input.gasAvailable := by
    change UInt256.mk (input.gasAvailable.val-0)=input.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' input .CODESIZE=2 := rfl
  have gas : ¬input.gasAvailable.toNat < 2 := by change ¬(u 9).toNat < 2;decide +kernel
  have capacity : input.stack.length+1 > 1024 := by change tail.length+1>1024;omega
  have gate : Assembly.driverGate #[] input .CODESIZE = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,reduceCtorEq,false_and,if_false,
      Nat.sub_zero,if_neg (Nat.not_lt_zero _),if_neg gas,if_pos capacity]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc=some (.CODESIZE,none) := DecoderAgreement.decode_all _
  change Assembly.driverSteps 1 2 #[] input = _
  simp only [Assembly.driverSteps]
  rw [decoded]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]

theorem capacity_refusal : Assembly.driverSteps 1 2 #[]
    (site .CODESIZE 9 3 (List.replicate 1024 (u 513))).state = .error .StackOverflow := by
  apply capacity_error
  rw [List.length_replicate]

theorem stack_boundary : Assembly.driverSteps 1 2 #[]
    (site .CODESIZE 9 3 (List.replicate 1023 (u 513))).state =
    .ok (expected (site .CODESIZE 9 3 (List.replicate 1023 (u 513))) (u 5)) := by
  have room : (site .CODESIZE 9 3 (List.replicate 1023 (u 513))).state.stack.length+1≤1024 := by
    change (List.replicate 1023 (u 513)).length+1≤1024
    rw [List.length_replicate]
  have h := (codesize_agreement _ 0 (by decide +kernel) room).1
  rw [normalize _ _ rfl rfl rfl] at h
  exact h

#print axioms populated
#print axioms ordered_code
#print axioms not_pc_or_remaining_extent
#print axioms suffix_included
#print axioms suffix_order
#print axioms gas_refusal
#print axioms fuel_precedes_gas
#print axioms capacity_refusal
#print axioms stack_boundary
end SolidityBridge.RoadmapV15.P10.CodeExtentControls
