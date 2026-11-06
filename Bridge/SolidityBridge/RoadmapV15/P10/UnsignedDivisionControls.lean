import SolidityBridge.RoadmapV15.P10.UnsignedDivisionConsumer

/-! Populated complete-State unsigned quotient/remainder and refusal controls.
Unsigned observations do not discharge source guards or compiler-origin premises. -/
namespace SolidityBridge.RoadmapV15.P10.UnsignedDivisionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def w (n : Nat) : Scalar.Word := BitVec.ofNat 256 n
private def spill : Scalar.Stack := [258,513]
private def seed (gas : Nat) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,activeWords := u 3
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := true,calldata := ⟨#[0x11,0x22,0x33]⟩}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
private def site (op : Backend.Op) (gas : Nat) (words : Scalar.Stack) : Site op :=
  modularSite ⟨seed gas,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .STOP],by decide⟩ words
private def expected {op : Backend.Op} (input : Site op) (words : Scalar.Stack) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42
    stack := words.map (fun x => UInt256.mk x.toFin)}

private theorem execute_div (a b value : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (result : (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat)) = value) :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (a::b::tail)).state =
      .ok (expected (site .DIV 5 (a::b::tail)) (value::tail)) := by
  let base : Site .DIV := ⟨seed 5,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .STOP],by decide⟩
  have h := (div_agreement base a b tail room (by change 5 ≤ 5;decide) 0).2.1
  rw [result] at h
  simpa only [base,site,expected,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u] using h

private theorem execute_mod (a b value : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (result : (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat)) = value) :
    Assembly.driverSteps 1 2 #[] (site .MOD 5 (a::b::tail)).state =
      .ok (expected (site .MOD 5 (a::b::tail)) (value::tail)) := by
  let base : Site .MOD := ⟨seed 5,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .STOP],by decide⟩
  have h := (mod_agreement base a b tail room (by change 5 ≤ 5;decide) 0).2.1
  rw [result] at h
  simpa only [base,site,expected,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u] using h

theorem quotient :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (w (7)::w (3)::spill)).state =
      .ok (expected (site .DIV 5 (w (7)::w (3)::spill)) (w (2)::spill)) := by
  exact execute_div _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem remainder :
    Assembly.driverSteps 1 2 #[] (site .MOD 5 (w (7)::w (3)::spill)).state =
      .ok (expected (site .MOD 5 (w (7)::w (3)::spill)) (w (1)::spill)) := by
  exact execute_mod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem high_unsigned :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (w (2^256-1)::w (2)::spill)).state =
      .ok (expected (site .DIV 5 (w (2^256-1)::w (2)::spill)) (w (2^255-1)::spill)) := by
  exact execute_div _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem high_remainder :
    Assembly.driverSteps 1 2 #[] (site .MOD 5 (w (2^256-1)::w (2)::spill)).state =
      .ok (expected (site .MOD 5 (w (2^256-1)::w (2)::spill)) (w (1)::spill)) := by
  exact execute_mod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem zero_divisor :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (w (7)::w (0)::spill)).state =
      .ok (expected (site .DIV 5 (w (7)::w (0)::spill)) (w (0)::spill)) := by
  exact execute_div _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem zero_modulus :
    Assembly.driverSteps 1 2 #[] (site .MOD 5 (w (7)::w (0)::spill)).state =
      .ok (expected (site .MOD 5 (w (7)::w (0)::spill)) (w (0)::spill)) := by
  exact execute_mod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem zero_dividend :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (w (0)::w (7)::spill)).state =
      .ok (expected (site .DIV 5 (w (0)::w (7)::spill)) (w (0)::spill)) := by
  exact execute_div _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem equal_maximum :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (w (2^256-1)::w (2^256-1)::spill)).state =
      .ok (expected (site .DIV 5 (w (2^256-1)::w (2^256-1)::spill)) (w (1)::spill)) := by
  exact execute_div _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem maximum_mod_one :
    Assembly.driverSteps 1 2 #[] (site .MOD 5 (w (2^256-1)::w (1)::spill)).state =
      .ok (expected (site .MOD 5 (w (2^256-1)::w (1)::spill)) (w (0)::spill)) := by
  exact execute_mod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem full_stack_boundary :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (7::3::List.replicate 1022 258)).state =
      .ok (expected (site .DIV 5 (7::3::List.replicate 1022 258)) (2::List.replicate 1022 258)) := by
  exact execute_div _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem gas_before_arity :
    Assembly.driverSteps 1 2 #[] (site .DIV 4 []).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (site .DIV 5 []).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem fuel_before_gas :
    Assembly.driverSteps 1 1 #[] (site .MOD 0 []).state = .error .OutOfFuel := by rfl

theorem wrong_signed_interpretation :
    Scalar.step (.op .DIV) [w (2^256-1),2] ≠ some [0] := by decide +kernel

theorem wrong_operand_order :
    Scalar.step (.op .DIV) [7,3] ≠ Scalar.step (.op .DIV) [3,7] := by decide +kernel

theorem wrong_remainder :
    Scalar.step (.op .MOD) [7,3] ≠ some [2] := by decide +kernel

theorem ordered_state_observations :
    (site .DIV 5 (7::3::spill)).state.executionEnv.code.data.toList = [0x60,0x05,0x50,0x04,0x00] ∧
    (expected (site .DIV 5 (7::3::spill)) (2::spill)).stack = [u 2,u 258,u 513] ∧
    (expected (site .DIV 5 (7::3::spill)) (2::spill)).memory.data.toList = [0xaa,0xbb] ∧
    (expected (site .DIV 5 (7::3::spill)) (2::spill)).returnData.data.toList = [0xcc,0xdd] ∧
    (expected (site .DIV 5 (7::3::spill)) (2::spill)).H_return.data.toList = [0xee,0xff] ∧
    (expected (site .DIV 5 (7::3::spill)) (2::spill)).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by decide +kernel

theorem output_capacity_refusal :
    Assembly.driverSteps 1 2 #[] (site .DIV 5 (7::3::List.replicate 1024 258)).state =
      .error .StackOverflow := by
  let base : Site .DIV := ⟨seed 5,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .STOP],by decide⟩
  exact div_capacity_refusal base 7 3 (List.replicate 1024 258)
    (by change 5 ≤ 5;decide) (by simp only [List.length_replicate];decide) 0

#print axioms output_capacity_refusal
#print axioms quotient
#print axioms remainder
#print axioms high_unsigned
#print axioms high_remainder
#print axioms zero_divisor
#print axioms zero_modulus
#print axioms zero_dividend
#print axioms equal_maximum
#print axioms maximum_mod_one
#print axioms full_stack_boundary
#print axioms gas_before_arity
#print axioms fuel_before_gas
#print axioms wrong_signed_interpretation
#print axioms wrong_operand_order
#print axioms wrong_remainder
#print axioms ordered_state_observations
end SolidityBridge.RoadmapV15.P10.UnsignedDivisionControls
