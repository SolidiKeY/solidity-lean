import SolidityBridge.RoadmapV15.P10.SignExtensionConsumer
namespace SolidityBridge.RoadmapV15.P10.SignExtensionControls
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
private def site (gas : Nat := 9) : Site .SIGNEXTEND :=
  ⟨seed gas 3 spill,[.push ⟨1,by decide⟩ #v[0x58],.op .POP],[.op .STOP],by decide⟩
private def input (index value : Nat) (gas : Nat := 9) : EVM.State :=
  (modularSite (site gas) [BitVec.ofNat 256 index,BitVec.ofNat 256 value,258,513]).state
private def expected (index value result : Nat) : EVM.State :=
  {input index value with
    gasAvailable := u 4,pc := u 4,execLength := 42
    stack := [u result,u 258,u 513]}

private theorem observed (index value result : Nat)
    (word : UInt256.signextend (u index) (u value)=u result) :
    Assembly.driverSteps 1 2 #[] (input index value) = .ok (expected index value result) := by
  have h := (signextend_fetched (site 9) (BitVec.ofNat 256 index) (BitVec.ofNat 256 value)
    [258,513] (by decide +kernel) (by decide +kernel) 0).1
  change Assembly.driverSteps 1 2 #[] (input index value) =
    .ok {input index value with
      gasAvailable := u 9-u 5,pc := u 3+u 1,execLength := 42
      stack := [UInt256.signextend (u index) (u value),u 258,u 513]} at h
  rw [word,show u 9-u 5=u 4 from by decide +kernel,
    show u 3+u 1=u 4 from by decide +kernel] at h
  exact h

theorem zero : Assembly.driverSteps 1 2 #[] (input 0 0) =
    .ok (expected 0 0 0) := by
  apply observed
  decide +kernel

theorem positive : Assembly.driverSteps 1 2 #[] (input 0 127) =
    .ok (expected 0 127 127) := by
  apply observed
  decide +kernel

theorem negative_byte : Assembly.driverSteps 1 2 #[] (input 0 128) =
    .ok (expected 0 128 (2^256-128)) := by
  apply observed
  decide +kernel

theorem narrow_truncation : Assembly.driverSteps 1 2 #[] (input 0 511) =
    .ok (expected 0 511 (2^256-1)) := by
  apply observed
  decide +kernel

theorem two_byte_index : Assembly.driverSteps 1 2 #[] (input 1 128) =
    .ok (expected 1 128 128) := by
  apply observed
  decide +kernel

theorem last_byte : Assembly.driverSteps 1 2 #[] (input 31 (2^255)) =
    .ok (expected 31 (2^255) (2^255)) := by
  apply observed
  decide +kernel

theorem first_outside : Assembly.driverSteps 1 2 #[] (input 32 (2^256-1)) =
    .ok (expected 32 (2^256-1) (2^256-1)) := by
  apply observed
  decide +kernel

theorem maximum_index : Assembly.driverSteps 1 2 #[] (input (2^256-1) 513) =
    .ok (expected (2^256-1) 513 513) := by
  apply observed
  decide +kernel

theorem ordered_code : (input 0 128).executionEnv.code.data.toList =
    [0x60,0x58,0x50,0x0b,0x00] := rfl

theorem index_is_bytes : Assembly.driverSteps 1 2 #[] (input 0 128) ≠
    .ok (expected 0 128 128) := by
  rw [negative_byte]
  intro h
  have top := congrArg (fun o => o.toOption.map (·.stack.head?)) h
  change some (some (u (2^256-128))) = some (some (u 128)) at top
  exact (by decide +kernel : u (2^256-128) ≠ u 128) (Option.some.inj (Option.some.inj top))

theorem scalar_narrow_controls :
    Scalar.run (Scalar.signedCode ⟨0,by decide⟩) [128,258,513] =
      some [BitVec.ofInt 256 (-128),258,513] ∧
    Scalar.run (Scalar.signedCode ⟨1,by decide⟩) [128,258,513] = some [128,258,513] := by
  constructor <;> decide +kernel

theorem gas_refusal : Assembly.driverSteps 1 2 #[] (input 0 128 4) = .error .OutOfGass := rfl

theorem fuel_precedes_gas : Assembly.driverSteps 1 1 #[] (input 0 128 0) = .error .OutOfFuel := rfl

private def short (gas : Nat) : EVM.State := (modularSite (site gas) [128]).state

theorem gas_precedes_stack : Assembly.driverSteps 1 2 #[] (short 4) = .error .OutOfGass := rfl

theorem stack_refusal : Assembly.driverSteps 1 2 #[] (short 9) = .error .StackUnderflow := rfl

theorem large_composed :
    Scalar.step (.op .SIGNEXTEND) [32,511,258,513] = some [511,258,513] ∧
    Assembly.driverSteps 1 2 #[] (input 32 511) = .ok (expected 32 511 511) := by
  have h := signextend_large_agreement (site 9) 32 511 [258,513]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0
  refine ⟨h.1,?_⟩
  have run := h.2.1
  change Assembly.driverSteps 1 2 #[] (input 32 511) =
    .ok {input 32 511 with
      gasAvailable := u 9-u 5,pc := u 3+u 1,execLength := 42
      stack := [u 511,u 258,u 513]} at run
  rw [show u 9-u 5=u 4 from by decide +kernel,
    show u 3+u 1=u 4 from by decide +kernel] at run
  exact run

theorem stack_boundary :
    let tail : Scalar.Stack := List.replicate 1022 513
    let start := (modularSite (site 9) (32::511::tail)).state
    Assembly.driverSteps 1 2 #[] start = .ok
      ((Assembly.chargedPrepare start 5).replaceStackAndIncrPC
        ((511::tail).map (fun w => UInt256.mk w.toFin))) := by
  have room : (List.replicate 1022 (513 : Scalar.Word)).length+2 ≤ 1024 := by
    rw [List.length_replicate]
  exact (signextend_large_agreement (site 9) 32 511 (List.replicate 1022 513)
    (by decide +kernel) room (by decide +kernel) 0).2.1

private theorem overflow_tail (tail : Scalar.Stack) (large : 1024 ≤ tail.length) :
    Assembly.driverSteps 1 2 #[] (modularSite (site 9) (32::511::tail)).state =
      .error .StackOverflow := by
  let start := (modularSite (site 9) (32::511::tail)).state
  have expansion : EVM.memoryExpansionCost start .SIGNEXTEND = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : start.gasAvailable-UInt256.ofNat 0=start.gasAvailable := by
    change UInt256.mk (start.gasAvailable.val-0)=start.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' start .SIGNEXTEND=5 := rfl
  have gas : ¬start.gasAvailable.toNat < 5 := by change ¬(u 9).toNat<5;decide +kernel
  have enough : ¬start.stack.length<2 := by
    change ¬((32::511::tail).map (fun w => UInt256.mk w.toFin)).length<2
    simp only [List.length_map,List.length_cons];omega
  have capacity : start.stack.length-2+1>1024 := by
    change ((32::511::tail).map (fun w => UInt256.mk w.toFin)).length-2+1>1024
    simp only [List.length_map,List.length_cons];omega
  have gate : Assembly.driverGate #[] start .SIGNEXTEND = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,reduceCtorEq,false_and,if_false,
      if_neg (Nat.not_lt_zero _),if_neg gas,if_neg enough,if_pos capacity]
    rfl
  have decoded : EVM.decode start.executionEnv.code start.pc=some (.SIGNEXTEND,none) :=
    DecoderAgreement.decode_all (modularSite (site 9) (32::511::tail))
  change Assembly.driverSteps 1 2 #[] start = _
  simp only [Assembly.driverSteps]
  rw [decoded]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]

theorem capacity_refusal : Assembly.driverSteps 1 2 #[]
    (modularSite (site 9) (32::511::List.replicate 1024 513)).state = .error .StackOverflow := by
  apply overflow_tail
  rw [List.length_replicate]

#print axioms large_composed
#print axioms stack_boundary
#print axioms capacity_refusal
#print axioms zero
#print axioms positive
#print axioms negative_byte
#print axioms narrow_truncation
#print axioms two_byte_index
#print axioms last_byte
#print axioms first_outside
#print axioms maximum_index
#print axioms ordered_code
#print axioms index_is_bytes
#print axioms scalar_narrow_controls
#print axioms gas_refusal
#print axioms fuel_precedes_gas
#print axioms gas_precedes_stack
#print axioms stack_refusal
end SolidityBridge.RoadmapV15.P10.SignExtensionControls
