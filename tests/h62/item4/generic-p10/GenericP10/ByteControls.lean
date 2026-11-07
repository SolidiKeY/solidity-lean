import GenericP10.ByteFixture
namespace GenericP10.ByteControls
open SolidityBridge.RoadmapV15.P10
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
private def site (gas : Nat := 9) : Site .BYTE :=
  ⟨seed gas 3 spill,[.push ⟨1,by decide⟩ #v[0x58],.op .POP],[.op .STOP],by decide⟩
private def input (index value : Nat) (gas : Nat := 9) : EVM.State :=
  (modularSite (site gas) [BitVec.ofNat 256 index,BitVec.ofNat 256 value,258,513]).state
private def expected (index value result : Nat) : EVM.State :=
  {input index value with
    gasAvailable := u 6,pc := u 4,execLength := 42
    stack := [u result,u 258,u 513]}

private theorem observed (index value result : Nat)
    (word : UInt256.byteAt (u index) (u value)=u result) :
    Assembly.driverSteps 1 2 #[] (input index value) = .ok (expected index value result) := by
  have h : Assembly.driverSteps 1 2 #[] (input index value) =
      .ok {input index value with
        gasAvailable := u 9-u 3,pc := u 3+u 1,execLength := 42
        stack := [u result,u 258,u 513]} :=
    (GenericP10.execute (site 9) (BitVec.ofNat 256 index)
      (BitVec.ofNat 256 value) (BitVec.ofNat 256 result) word [258,513]
      (by decide +kernel) (by decide +kernel) 0).1
  rw [show u 9-u 3=u 6 from by decide +kernel,
    show u 3+u 1=u 4 from by decide +kernel] at h
  exact h

private def payload : Nat := 0x12*2^248+0x34*2^240+0x56*256+0x78
private def typed : PrimTy.uint.Denote := ⟨payload,by decide +kernel⟩


private theorem table_case (c : GenericP10.ByteCase) :
    Assembly.driverSteps 1 2 #[]
      (input (GenericP10.fixture c).index.val (GenericP10.fixture c).value.val) =
    .ok (expected (GenericP10.fixture c).index.val (GenericP10.fixture c).value.val
      (GenericP10.fixture c).result.val) :=
  observed _ _ _ (GenericP10.fixture c).word_eq

theorem first_byte : Assembly.driverSteps 1 2 #[] (input 0 payload) = .ok (expected 0 payload 0x12) := by
  exact table_case .first

theorem second_byte : Assembly.driverSteps 1 2 #[] (input 1 payload) = .ok (expected 1 payload 0x34) := by
  exact table_case .second

theorem middle_zero : Assembly.driverSteps 1 2 #[] (input 15 payload) = .ok (expected 15 payload 0) := by
  exact table_case .middle

theorem penultimate_byte : Assembly.driverSteps 1 2 #[] (input 30 payload) = .ok (expected 30 payload 0x56) := by
  exact table_case .penultimate

theorem last_byte : Assembly.driverSteps 1 2 #[] (input 31 payload) = .ok (expected 31 payload 0x78) := by
  exact table_case .last

theorem outside_word : Assembly.driverSteps 1 2 #[] (input 32 payload) = .ok (expected 32 payload 0) := by
  exact table_case .outside

theorem maximum_index : Assembly.driverSteps 1 2 #[] (input (2^256-1) payload) = .ok (expected (2^256-1) payload 0) := by
  exact table_case .maximumIndex

theorem zero_word : Assembly.driverSteps 1 2 #[] (input 0 0) = .ok (expected 0 0 0) := by
  exact table_case .zero

theorem maximum_word : Assembly.driverSteps 1 2 #[] (input 31 (2^256-1)) = .ok (expected 31 (2^256-1) 255) := by
  exact table_case .maximumWord

theorem ordered_code : (input 0 payload).executionEnv.code.data.toList =
    [0x60,0x58,0x50,0x1a,0x00] := rfl

theorem ordered_word_bytes :
    List.ofFn (fun j : Fin 32 => Solidity.Evm.TryByteImage.wordByte typed j.val) =
      [0x12,0x34] ++ List.replicate 28 0 ++ [0x56,0x78] := by decide +kernel

theorem wrong_endian : Assembly.driverSteps 1 2 #[] (input 0 payload) ≠
    .ok (expected 0 payload 0x78) := by
  rw [first_byte]
  intro h
  have top := congrArg (fun o => o.toOption.map (·.stack.head?)) h
  change some (some (u 0x12)) = some (some (u 0x78)) at top
  exact (by decide +kernel : u 0x12 ≠ u 0x78) (Option.some.inj (Option.some.inj top))

theorem typed_image_client :
    let start := (modularSite (site 9) (0::Scalar.encodeValue .uint typed::[258,513])).state
    Assembly.driverSteps 1 2 #[] start = .ok
      ((Assembly.chargedPrepare start 3).replaceStackAndIncrPC [u 0x12,u 258,u 513]) := by
  have h := (byte_image_agreement (site 9) typed ⟨0,by decide⟩ [258,513]
    (by decide +kernel) (by decide +kernel) 0).1
  have value : (Solidity.Evm.TryByteImage.wordByte typed 0).toNat = 0x12 := by decide +kernel
  dsimp only at h ⊢
  rw [value] at h
  exact h

theorem stack_boundary :
    let tail : Scalar.Stack := List.replicate 1022 513
    let start := (modularSite (site 9) (32::511::tail)).state
    Assembly.driverSteps 1 2 #[] start = .ok
      ((Assembly.chargedPrepare start 3).replaceStackAndIncrPC
        (u 0 :: tail.map (fun w => UInt256.mk w.toFin))) := by
  have room : (List.replicate 1022 (513 : Scalar.Word)).length+2 ≤ 1024 := by rw [List.length_replicate]
  have h := (byte_fetched (site 9) 32 511 (List.replicate 1022 513) room (by decide +kernel) 0).1
  have word : UInt256.byteAt ⟨(32 : Scalar.Word).toFin⟩ ⟨(511 : Scalar.Word).toFin⟩ = u 0 :=
    byte_large _ _ (by decide +kernel)
  dsimp only at h ⊢
  rw [word] at h
  exact h

theorem gas_refusal : Assembly.driverSteps 1 2 #[] (input 0 payload 2) = .error .OutOfGass := rfl

theorem fuel_precedes_gas : Assembly.driverSteps 1 1 #[] (input 0 payload 0) = .error .OutOfFuel := rfl

private def short (gas : Nat) : EVM.State := (modularSite (site gas) [128]).state

theorem gas_precedes_stack : Assembly.driverSteps 1 2 #[] (short 2) = .error .OutOfGass := rfl

theorem stack_refusal : Assembly.driverSteps 1 2 #[] (short 9) = .error .StackUnderflow := rfl

private theorem overflow_tail (tail : Scalar.Stack) (large : 1024 ≤ tail.length) :
    Assembly.driverSteps 1 2 #[] (modularSite (site 9) (32::511::tail)).state =
      .error .StackOverflow := by
  let start := (modularSite (site 9) (32::511::tail)).state
  have expansion : EVM.memoryExpansionCost start .BYTE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : start.gasAvailable-UInt256.ofNat 0=start.gasAvailable := by
    change UInt256.mk (start.gasAvailable.val-0)=start.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' start .BYTE=3 := rfl
  have gas : ¬start.gasAvailable.toNat < 3 := by change ¬(u 9).toNat<3;decide +kernel
  have enough : ¬start.stack.length<2 := by
    change ¬((32::511::tail).map (fun w => UInt256.mk w.toFin)).length<2
    simp only [List.length_map,List.length_cons];omega
  have capacity : start.stack.length-2+1>1024 := by
    change ((32::511::tail).map (fun w => UInt256.mk w.toFin)).length-2+1>1024
    simp only [List.length_map,List.length_cons];omega
  have gate : Assembly.driverGate #[] start .BYTE = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,reduceCtorEq,false_and,if_false,
      if_neg (Nat.not_lt_zero _),if_neg gas,if_neg enough,if_pos capacity]
    rfl
  have decoded : EVM.decode start.executionEnv.code start.pc=some (.BYTE,none) :=
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

theorem image_index_requires_bound :
    Solidity.Evm.TryByteImage.wordByte typed 32 = 0x78 ∧
    Assembly.driverSteps 1 2 #[] (input 32 payload) = .ok (expected 32 payload 0) := by
  exact ⟨by decide +kernel,outside_word⟩

theorem scalar_refusal_control :
    Scalar.step (.op .BYTE) [0,Scalar.encodeValue .uint typed,258,513] = none :=
  byte_scalar_refusal _ _ _

#print axioms image_index_requires_bound
#print axioms scalar_refusal_control
#print axioms first_byte
#print axioms second_byte
#print axioms middle_zero
#print axioms penultimate_byte
#print axioms last_byte
#print axioms outside_word
#print axioms maximum_index
#print axioms zero_word
#print axioms maximum_word
#print axioms ordered_code
#print axioms ordered_word_bytes
#print axioms wrong_endian
#print axioms typed_image_client
#print axioms stack_boundary
#print axioms gas_refusal
#print axioms fuel_precedes_gas
#print axioms gas_precedes_stack
#print axioms stack_refusal
#print axioms capacity_refusal
end GenericP10.ByteControls
