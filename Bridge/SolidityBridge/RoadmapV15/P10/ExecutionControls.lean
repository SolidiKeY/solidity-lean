import SolidityBridge.RoadmapV15.P10.Execution
import Solidity.Backend.Jumpdest

/-! Exact populated source-byte/fetched execution witnesses. Nonzero COPY keeps
its actual opaque memory expression; it is not a physical-padding witness. -/
namespace SolidityBridge.RoadmapV15.P10.ExecutionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def seed (gas : Nat) (stack : List UInt256) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,stack := stack,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := true}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41} |>.insert (.ofNat 19)
      {(default : Account .EVM) with nonce := u 6,balance := u 43}}
private def site (op : Backend.Op) (gas : Nat) (stack : List UInt256) : Site op :=
  ⟨seed gas stack,[.push ⟨1,by decide⟩ #v[0x5b],.op .POP],[.op .POP,.op .JUMPDEST],by decide⟩
private def tail : List UInt256 := [u 258,u 513]
private def valid : Array UInt256 := #[u 5]
private def observe (s : EVM.State) :=
  (s.pc.toNat,s.gasAvailable.toNat,s.execLength,s.stack.map UInt256.toNat,
   s.memory.data.toList,s.returnData.data.toList,s.H_return.data.toList,s.activeWords.toNat,
   s.executionEnv.code.data.toList,(s.accountMap.find! (.ofNat 7)).nonce.toNat,
   (s.accountMap.find! (.ofNat 7)).balance.toNat,(s.accountMap.find! (.ofNat 11)).balance.toNat,
   (s.accountMap.find! (.ofNat 19)).balance.toNat,
   ((s.accountMap.find? (.ofNat 31)).map (fun a => a.balance.toNat)).getD 0,
   s.executionEnv.codeOwner.val,s.executionEnv.source.val,s.executionEnv.sender.val,s.executionEnv.perm)

-- Actual successful, nonzero-value account CALL to an empty non-precompile account.
theorem funded_call :
    (Assembly.driverSteps 1 7 valid (site .CALL 100000
      (u 0::u 31::u 7::u 0::u 0::u 0::u 0::tail)).state).map observe =
    .ok (4,65700,42,[1,258,513],[0xaa,0xbb],[],[0xee,0xff],1,[0x60,0x5b,0x50,0xf1,0x50,0x5b],3,22,41,43,7,7,11,19,true) := by
  rw [checked_call]
  rfl

theorem underfunded_call :
    (Assembly.driverSteps 1 7 valid (site .CALL 100000
      (u 0::u 31::u 30::u 0::u 0::u 0::u 0::tail)).state).map observe =
    .ok (4,65700,42,[0,258,513],[0xaa,0xbb],[],[0xee,0xff],1,[0x60,0x5b,0x50,0xf1,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_call]
  rfl

theorem return_size :
    (Assembly.driverSteps 1 2 valid (site .RETURNDATASIZE 2 tail).state).map observe =
    .ok (4,0,42,[2,258,513],[0xaa,0xbb],[0xcc,0xdd],[0xee,0xff],1,[0x60,0x5b,0x50,0x3d,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_return_size]
  rfl

theorem copy_boundary_empty :
    (Assembly.driverSteps 1 2 valid (site .RETURNDATACOPY 3 (u 0::u 2::u 0::tail)).state).map observe =
    .ok (4,0,42,[258,513],[0xaa,0xbb],[0xcc,0xdd],[0xee,0xff],1,[0x60,0x5b,0x50,0x3e,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_return_copy]
  rfl

/-- Actual nonempty copy execution: opaque allocator data is retained exactly,
without asserting zeroes0=empty or replacing the expected memory bytes. -/
theorem copy_nonempty :
    (Assembly.driverSteps 1 2 valid (site .RETURNDATACOPY 6 (u 0::u 0::u 1::tail)).state).map observe =
    .ok (4,0,42,[258,513],(ByteArray.write ⟨#[0xcc,0xdd]⟩ 0 ⟨#[0xaa,0xbb]⟩ 0 1).data.toList,
      [0xcc,0xdd],[0xee,0xff],1,[0x60,0x5b,0x50,0x3e,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_return_copy]
  rfl

theorem jump_taken :
    (Assembly.driverSteps 1 2 valid (site .JUMP 8 (u 5::tail)).state).map observe =
    .ok (5,0,42,[258,513],[0xaa,0xbb],[0xcc,0xdd],[0xee,0xff],1,[0x60,0x5b,0x50,0x56,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_jump]
  rfl

theorem jump_if_taken :
    (Assembly.driverSteps 1 2 valid (site .JUMPI 10 (u 5::u 7::tail)).state).map observe =
    .ok (5,0,42,[258,513],[0xaa,0xbb],[0xcc,0xdd],[0xee,0xff],1,[0x60,0x5b,0x50,0x57,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_jump_if]
  rfl

theorem jump_if_skipped :
    (Assembly.driverSteps 1 2 valid (site .JUMPI 10 (u 1::u 0::tail)).state).map observe =
    .ok (4,0,42,[258,513],[0xaa,0xbb],[0xcc,0xdd],[0xee,0xff],1,[0x60,0x5b,0x50,0x57,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_jump_if]
  rfl

theorem jump_dest :
    (Assembly.driverSteps 1 2 #[u 3,u 5] (site .JUMPDEST 1 tail).state).map observe =
    .ok (4,0,42,[258,513],[0xaa,0xbb],[0xcc,0xdd],[0xee,0xff],1,[0x60,0x5b,0x50,0x5b,0x50,0x5b],3,29,41,43,0,7,11,19,true) := by
  rw [checked_jump_dest]
  rfl

-- Supplied jump arrays match the actual backend byte scanner for these images.
example : Backend.jumpdests (Backend.encode ((site .JUMPI 10 []).before ++ .op .JUMPI :: (site .JUMPI 10 []).after)) = [5] := by
  change Backend.jumpdests [0x60,0x5b,0x50,0x57,0x50,0x5b] = [5]
  have push : Backend.immWidth (0x60 : UInt8) = 1 := rfl
  have pop : Backend.immWidth (0x50 : UInt8) = 0 := rfl
  have branch : Backend.immWidth (0x57 : UInt8) = 0 := rfl
  have dest : Backend.immWidth (0x5b : UInt8) = 0 := rfl
  simp only [Backend.jumpdests,Backend.starts,push,pop,branch,dest,List.drop_succ_cons,List.drop_zero]
  decide +kernel
example : Backend.InPushData (Backend.encode ((site .JUMP 8 []).before ++ .op .JUMP :: (site .JUMP 8 []).after)) 1 := by
  refine ⟨0,?_,0x60,by decide,by decide,by decide⟩
  change 0 ∈ Backend.starts [0x60,0x5b,0x50,0x56,0x50,0x5b]
  rw [Backend.starts]
  exact List.mem_cons_self
example : Assembly.driverSteps 1 2 valid (site .JUMP 8 (u 1::tail)).state = .error .BadJumpDestination := by rfl
example : Assembly.driverSteps 1 2 valid (site .JUMPI 10 (u 1::u 1::tail)).state = .error .BadJumpDestination := by rfl
example : Assembly.driverSteps 1 2 valid (site .JUMP 0 []).state = .error .OutOfGass := by rfl
example : Assembly.driverSteps 1 2 valid (site .JUMP 8 []).state = .error .StackUnderflow := by rfl
example : Assembly.driverSteps 1 2 valid (site .RETURNDATACOPY 6 (u 0::u 2::u 1::tail)).state = .error .InvalidMemoryAccess := by rfl
example : Assembly.driverSteps 1 2 valid (site .RETURNDATACOPY 3 (u 0::u 3::u 0::tail)).state = .error .InvalidMemoryAccess := by rfl
example : Assembly.driverSteps 1 2 valid (site .RETURNDATACOPY 2 (u 0::u 2::u 1::tail)).state = .error .OutOfGass := by rfl
example : Assembly.driverSteps 1 2 valid (site .CALL 0 []).state = .error .OutOfGass := by rfl
example : Assembly.driverSteps 1 2 valid (site .CALL 100000 []).state = .error .StackUnderflow := by rfl
private def staticSite (value : UInt256) : Site .CALL :=
  {site .CALL 100000 (u 0::u 31::value::u 0::u 0::u 0::u 0::tail) with
    seed := {seed 100000 (u 0::u 31::value::u 0::u 0::u 0::u 0::tail) with
      executionEnv := {(seed 100000 []).executionEnv with perm := false}}}
example : Assembly.driverSteps 1 2 valid (staticSite (u 7)).state = .error .StaticModeViolation := by rfl

example : Assembly.driverSteps 1 2 valid (site .CALL 100000 (u 0::u 31::u 7::u 0::u 0::u 0::u 0::tail)).state = .error .OutOfFuel := by rfl
example : Assembly.driverSteps 1 1 valid (site .JUMP 8 (u 5::tail)).state = .error .OutOfFuel := by rfl
theorem static_zero_call :
    (Assembly.driverSteps 1 7 valid (staticSite (u 0)).state).map observe =
    .ok (4,97400,42,[1,258,513],[0xaa,0xbb],[],[0xee,0xff],1,[0x60,0x5b,0x50,0xf1,0x50,0x5b],3,29,41,43,0,7,11,19,false) := by
  rw [checked_call]
  rfl

-- The only push in this family retains the real overflow check.
example : Assembly.driverSteps 1 2 valid
    (site .RETURNDATASIZE 2 (List.replicate 1024 (u 513))).state = .error .StackOverflow := by
  let image := site .RETURNDATASIZE 2 (List.replicate 1024 (u 513))
  have length : image.state.stack.length = 1024 := by
    change (List.replicate 1024 (u 513)).length = 1024
    rw [List.length_replicate]
  have expansion : EVM.memoryExpansionCost image.state .RETURNDATASIZE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : image.state.gasAvailable - UInt256.ofNat 0 = image.state.gasAvailable := by
    change u 2 - UInt256.ofNat 0 = u 2
    decide +kernel
  have gate : Assembly.driverGate valid image.state .RETURNDATASIZE = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    have cost : EVM.C' image.state .RETURNDATASIZE = 2 := rfl
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,length]
    rfl
  rw [checked_return_size image valid 0,gate]

#print axioms Site.recover
#print axioms dispatch_call
#print axioms dispatch_return_size
#print axioms dispatch_return_copy
#print axioms dispatch_jump
#print axioms dispatch_jump_if
#print axioms dispatch_jump_dest
#print axioms checked_call
#print axioms checked_return_size
#print axioms checked_return_copy
#print axioms checked_jump
#print axioms checked_jump_if
#print axioms checked_jump_dest
#print axioms x_call
#print axioms x_return_size
#print axioms x_return_copy
#print axioms x_jump
#print axioms x_jump_if
#print axioms x_jump_dest
#print axioms jump_dest
#print axioms static_zero_call
#print axioms funded_call
#print axioms underfunded_call
#print axioms return_size
#print axioms copy_boundary_empty
#print axioms copy_nonempty
#print axioms jump_taken
#print axioms jump_if_taken
#print axioms jump_if_skipped
end SolidityBridge.RoadmapV15.P10.ExecutionControls
