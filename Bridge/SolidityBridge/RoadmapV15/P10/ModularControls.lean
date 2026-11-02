import SolidityBridge.RoadmapV15.P10.Modular

/-! Complete State witnesses, including ordered buffers and account context.
No source/frame origin or production Osaka adequacy follows from these fixtures. -/
namespace SolidityBridge.RoadmapV15.P10.ModularControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def maximum : Scalar.Word := BitVec.ofNat 256 (2^256-1)
private def spill : Scalar.Stack := [258,513]
private def seed (gas : Nat) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := false}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
private def site (op : Backend.Op) (gas : Nat) (words : Scalar.Stack) : Site op :=
  modularSite ⟨seed gas,[.push ⟨1,by decide⟩ #v[0x09],.op .POP],[.op .STOP],by decide⟩ words
private def expected {op : Backend.Op} (input : Site op) (words : Scalar.Stack) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42
    stack := words.map (fun w => UInt256.mk w.toFin)}

theorem add_full_precision :
    Scalar.step (.op .ADDMOD) [maximum,1,7] = some [2] ∧
    Assembly.driverSteps 1 2 #[] (site .ADDMOD 8 (maximum::1::7::spill)).state =
      .ok (expected (site .ADDMOD 8 (maximum::1::7::spill)) (2::spill)) := by
  constructor <;> rfl

theorem mul_full_precision :
    Scalar.step (.op .MULMOD) [maximum,2,7] = some [2] ∧
    Assembly.driverSteps 1 2 #[] (site .MULMOD 8 (maximum::2::7::spill)).state =
      .ok (expected (site .MULMOD 8 (maximum::2::7::spill)) (2::spill)) := by
  constructor <;> rfl

theorem add_zero_modulus :
    Assembly.driverSteps 1 2 #[] (site .ADDMOD 8 (maximum::1::0::spill)).state =
      .ok (expected (site .ADDMOD 8 (maximum::1::0::spill)) (0::spill)) := by rfl

theorem mul_zero_modulus :
    Assembly.driverSteps 1 2 #[] (site .MULMOD 8 (maximum::2::0::spill)).state =
      .ok (expected (site .MULMOD 8 (maximum::2::0::spill)) (0::spill)) := by rfl

theorem maximum_modulus :
    Assembly.driverSteps 1 2 #[] (site .ADDMOD 8 (maximum::maximum::maximum::spill)).state =
      .ok (expected (site .ADDMOD 8 (maximum::maximum::maximum::spill)) (0::spill)) := by rfl

-- Keep the complete caller list abstract in the proof; its inhabitant follows.
private theorem boundary_tail (tail : Scalar.Stack) (length : tail.length = 1021) :
    Assembly.driverSteps 1 2 #[] (site .ADDMOD 8 (1::2::7::tail)).state =
      .ok (expected (site .ADDMOD 8 (1::2::7::tail)) (3::tail)) := by
  let base : Site .ADDMOD := ⟨seed 8,[.push ⟨1,by decide⟩ #v[0x09],.op .POP],[.op .STOP],by decide⟩
  have room : tail.length+3 ≤ 1024 := by rw [length]
  have h := (addmod_agreement base 1 2 7 tail room (by decide +kernel) 0).2.1
  simpa only [base,expected,site,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,List.map_cons] using h

-- The complete1021-word caller tail is retained, not its length observation.
theorem stack_boundary :
    let tail : Scalar.Stack := List.replicate 1021 513
    Assembly.driverSteps 1 2 #[] (site .ADDMOD 8 (1::2::7::tail)).state =
      .ok (expected (site .ADDMOD 8 (1::2::7::tail)) (3::tail)) :=
  boundary_tail _ List.length_replicate

-- The actual gate checks output capacity, not initial stack legality.
-- A1022-tail would not overflow this local gate; use1024tail/1025output.
private theorem overflow_tail (tail : Scalar.Stack) (length : tail.length = 1024) :
    Assembly.driverSteps 1 2 #[]
      (site .ADDMOD 8 (1::2::7::tail)).state = .error .StackOverflow := by
  let image := site .ADDMOD 8 (1::2::7::tail)
  have count : image.state.stack.length = 1027 := by
    change ((1::2::7::tail).map (fun w : Scalar.Word => UInt256.mk w.toFin)).length = 1027
    simp only [List.length_map,List.length_cons,length]
  have expansion : EVM.memoryExpansionCost image.state .ADDMOD = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : image.state.gasAvailable-UInt256.ofNat 0 = image.state.gasAvailable := by
    change u 8-UInt256.ofNat 0 = u 8
    decide +kernel
  have gate : Assembly.driverGate #[] image.state .ADDMOD = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    have cost : EVM.C' image.state .ADDMOD = 8 := rfl
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,count]
    rfl
  change Assembly.driverSteps 1 2 #[] image.state = .error .StackOverflow
  simp only [Assembly.driverSteps]
  rw [decode_addmod image]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]


theorem fetched_stack_overflow :
    Assembly.driverSteps 1 2 #[]
      (site .ADDMOD 8 (1::2::7::List.replicate 1024 513)).state = .error .StackOverflow :=
  overflow_tail _ List.length_replicate


private def combination : Site .ADDMOD :=
  modularSite ⟨seed 16,[.push ⟨1,by decide⟩ #v[0x09],.op .POP],
    [.op .MULMOD,.op .STOP],by decide⟩ (maximum::1::7::3::5::spill)

theorem fetched_combination :
    Scalar.run [.op .ADDMOD,.op .MULMOD] (maximum::1::7::3::5::spill) = some (1::spill) ∧
    Assembly.driverSteps 2 3 #[] combination.state =
      .ok {combination.state with
        pc := u 5,gasAvailable := u 0,execLength := 43
        stack := (1::spill).map (fun w => UInt256.mk w.toFin)} := by
  constructor <;> rfl

-- Wrong intermediate truncation gives0, whereas actual full-precision results give2.
theorem wrong_wrapped_add :
    ((maximum+1).toNat % 7) = 0 ∧ Scalar.step (.op .ADDMOD) [maximum,1,7] ≠ some [0] := by
  constructor
  · rfl
  · decide +kernel

theorem wrong_wrapped_mul :
    ((maximum*2).toNat % 7) = 0 ∧ Scalar.step (.op .MULMOD) [maximum,2,7] ≠ some [0] := by
  constructor
  · rfl
  · decide +kernel

example : Assembly.driverSteps 1 2 #[] (site .ADDMOD 7 []).state = .error .OutOfGass := by rfl
example : Assembly.driverSteps 1 2 #[] (site .ADDMOD 8 [1,2]).state = .error .StackUnderflow := by rfl
example : Assembly.driverSteps 1 1 #[] (site .MULMOD 8 [maximum,2,7]).state = .error .OutOfFuel := by rfl
example : Scalar.step (.op .ADDMOD) [maximum,7,1] ≠ some [2] := by decide +kernel

#print axioms add_full_precision
#print axioms mul_full_precision
#print axioms add_zero_modulus
#print axioms mul_zero_modulus
#print axioms maximum_modulus
#print axioms stack_boundary
#print axioms fetched_stack_overflow
#print axioms fetched_combination
#print axioms wrong_wrapped_add
#print axioms wrong_wrapped_mul
end SolidityBridge.RoadmapV15.P10.ModularControls
