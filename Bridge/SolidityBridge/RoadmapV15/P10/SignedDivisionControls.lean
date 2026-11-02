import SolidityBridge.RoadmapV15.P10.SignedDivisionConsumer
import Solidity.Backend.Scalar.Widths

/-! Populated complete-State signed quotient/remainder and width controls.
Raw minimum divided by -1 wrap and zero are not source failure-policy conclusions. -/
namespace SolidityBridge.RoadmapV15.P10.SignedDivisionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def w (i : Int) : Scalar.Word := BitVec.ofInt 256 i
private def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
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
  modularSite ⟨seed gas,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .STOP],by decide⟩ words
private def expected {op : Backend.Op} (input : Site op) (words : Scalar.Stack) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42
    stack := words.map (fun x => UInt256.mk x.toFin)}

private theorem execute_sdiv (a b value : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (result : (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt)) = value) :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (a::b::tail)).state =
      .ok (expected (site .SDIV 5 (a::b::tail)) (value::tail)) := by
  let base : Site .SDIV := ⟨seed 5,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .STOP],by decide⟩
  have h := (sdiv_agreement base a b tail room (by change 5 ≤ 5;decide) 0).2.1
  rw [result] at h
  simpa only [base,site,expected,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u] using h

private theorem execute_smod (a b value : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (result : (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt)) = value) :
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (a::b::tail)).state =
      .ok (expected (site .SMOD 5 (a::b::tail)) (value::tail)) := by
  let base : Site .SMOD := ⟨seed 5,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .STOP],by decide⟩
  have h := (smod_agreement base a b tail room (by change 5 ≤ 5;decide) 0).2.1
  rw [result] at h
  simpa only [base,site,expected,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u] using h

theorem sdiv_positive_positive :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (w (7)::w (3)::spill)).state =
      .ok (expected (site .SDIV 5 (w (7)::w (3)::spill)) (w (2)::spill)) := by
  exact execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem sdiv_positive_negative :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (w (7)::w (-3)::spill)).state =
      .ok (expected (site .SDIV 5 (w (7)::w (-3)::spill)) (w (-2)::spill)) := by
  exact execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem sdiv_negative_positive :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (w (-7)::w (3)::spill)).state =
      .ok (expected (site .SDIV 5 (w (-7)::w (3)::spill)) (w (-2)::spill)) := by
  exact execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem sdiv_negative_negative :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (w (-7)::w (-3)::spill)).state =
      .ok (expected (site .SDIV 5 (w (-7)::w (-3)::spill)) (w (2)::spill)) := by
  exact execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem smod_positive_positive :
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (w (7)::w (3)::spill)).state =
      .ok (expected (site .SMOD 5 (w (7)::w (3)::spill)) (w (1)::spill)) := by
  exact execute_smod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem smod_positive_negative :
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (w (7)::w (-3)::spill)).state =
      .ok (expected (site .SMOD 5 (w (7)::w (-3)::spill)) (w (1)::spill)) := by
  exact execute_smod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem smod_negative_positive :
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (w (-7)::w (3)::spill)).state =
      .ok (expected (site .SMOD 5 (w (-7)::w (3)::spill)) (w (-1)::spill)) := by
  exact execute_smod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem smod_negative_negative :
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (w (-7)::w (-3)::spill)).state =
      .ok (expected (site .SMOD 5 (w (-7)::w (-3)::spill)) (w (-1)::spill)) := by
  exact execute_smod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem zero_divisor :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (w (-7)::0::spill)).state =
      .ok (expected (site .SDIV 5 (w (-7)::0::spill)) (0::spill)) ∧
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (w (-7)::0::spill)).state =
      .ok (expected (site .SMOD 5 (w (-7)::0::spill)) (0::spill)) := by
  exact ⟨execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel),
    execute_smod _ _ _ _ (by decide +kernel) (by decide +kernel)⟩

theorem minimum_wrap :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (minimum::w (-1)::spill)).state =
      .ok (expected (site .SDIV 5 (minimum::w (-1)::spill)) (minimum::spill)) := by
  exact execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem minimum_identity :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (minimum::1::spill)).state =
      .ok (expected (site .SDIV 5 (minimum::1::spill)) (minimum::spill)) := by
  exact execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem minimum_mod_zero :
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (minimum::w (-1)::spill)).state =
      .ok (expected (site .SMOD 5 (minimum::w (-1)::spill)) (0::spill)) := by
  exact execute_smod _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem signed_byte_truncation :
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 (w (-128)::w (-1)::spill)).state =
      .ok (expected (site .SDIV 5 (w (-128)::w (-1)::spill)) (128::spill)) ∧
    Scalar.signedClean ⟨0,by decide⟩ 128 = w (-128) := by
  exact ⟨execute_sdiv _ _ _ _ (by decide +kernel) (by decide +kernel),by decide +kernel⟩

theorem stack_boundary :
    Assembly.driverSteps 1 2 #[] (site .SMOD 5 (w (-7)::3::List.replicate 1022 513)).state =
      .ok (expected (site .SMOD 5 (w (-7)::3::List.replicate 1022 513))
        (w (-1)::List.replicate 1022 513)) := by
  apply execute_smod
  · simp only [List.length_replicate];decide
  · decide +kernel

private def combination : Site .SDIV :=
  modularSite ⟨seed 10,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .SMOD,.op .STOP],by decide⟩
    (w (-17)::3::3::spill)

theorem fetched_combination :
    Scalar.run [.op .SDIV,.op .SMOD] (w (-17)::3::3::spill) = some (w (-2)::spill) ∧
    Assembly.driverSteps 2 3 #[] combination.state =
      .ok {combination.state with
        pc := u 5,gasAvailable := u 0,execLength := 43
        stack := (w (-2)::spill).map (fun x => UInt256.mk x.toFin)} := by
  constructor
  · decide +kernel
  · let base : Site .SDIV := ⟨seed 10,[.push ⟨1,by decide⟩ #v[0x05],.op .POP],[.op .SMOD,.op .STOP],by decide⟩
    have first := (sdiv_agreement base (w (-17)) 3 (3::spill) (by decide +kernel)
      (by change 5 ≤ 10;decide) 1).2.1
    have result : (if (3 : Scalar.Word) == 0 then 0 else
        BitVec.ofInt 256 ((w (-17)).toInt.tdiv (3 : Scalar.Word).toInt)) = w (-5) := by decide +kernel
    rw [result] at first
    have first' : Assembly.driverSteps 1 3 #[] combination.state =
        .ok ((Assembly.chargedPrepare combination.state 5).replaceStackAndIncrPC
          ((w (-5)::3::spill).map (fun x => UInt256.mk x.toFin))) := by
      simpa only [combination,base] using first
    rw [fetched_steps_cons 1 1 #[] combination.state,first']
    rfl

theorem gas_before_arity :
    Assembly.driverSteps 1 2 #[] (site .SDIV 4 []).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (site .SDIV 5 []).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem fuel_refusal :
    Assembly.driverSteps 1 1 #[] (site .SMOD 5 (w (-7)::3::spill)).state = .error .OutOfFuel := by rfl

theorem wrong_quotient_rounding :
    Scalar.step (.op .SDIV) (w (-7)::3::spill) ≠ some (w (-3)::spill) := by decide +kernel

theorem wrong_remainder_sign :
    Scalar.step (.op .SMOD) (w (-7)::3::spill) ≠ some (1::spill) := by decide +kernel

theorem wrong_operand_order :
    Scalar.step (.op .SDIV) (w (-7)::3::spill) ≠ Scalar.step (.op .SDIV) (3::w (-7)::spill) := by decide +kernel

#print axioms sdiv_positive_positive
#print axioms sdiv_positive_negative
#print axioms sdiv_negative_positive
#print axioms sdiv_negative_negative
#print axioms smod_positive_positive
#print axioms smod_positive_negative
#print axioms smod_negative_positive
#print axioms smod_negative_negative
#print axioms zero_divisor
#print axioms minimum_wrap
#print axioms minimum_identity
#print axioms minimum_mod_zero
#print axioms signed_byte_truncation
#print axioms stack_boundary
#print axioms fetched_combination
#print axioms gas_before_arity
#print axioms fuel_refusal
#print axioms wrong_quotient_rounding
#print axioms wrong_remainder_sign
#print axioms wrong_operand_order
end SolidityBridge.RoadmapV15.P10.SignedDivisionControls
