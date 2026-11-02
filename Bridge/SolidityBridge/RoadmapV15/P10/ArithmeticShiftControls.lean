import SolidityBridge.RoadmapV15.P10.ArithmeticShiftConsumer

/-! Complete-State SAR controls, including saturated maximal word counts.
Floor division of negative odd words is distinguished from SDIV truncation. -/
namespace SolidityBridge.RoadmapV15.P10.ArithmeticShiftControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def w (i : Int) : Scalar.Word := BitVec.ofInt 256 i
private def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
private def maximum : Scalar.Word := BitVec.ofNat 256 (2^256-1)
private def positiveMaximum : Scalar.Word := BitVec.ofNat 256 (2^255-1)
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
private def site (gas : Nat) (words : Scalar.Stack) : Site .SAR :=
  modularSite ⟨seed gas,[.push ⟨1,by decide⟩ #v[0x1d],.op .POP],[.op .STOP],by decide⟩ words
private def expected (input : Site .SAR) (words : Scalar.Stack) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42
    stack := words.map (fun x => UInt256.mk x.toFin)}
private theorem execute (a b value : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024)
    (result : (if a.toNat < 256 then BitVec.ofInt 256 (b.toInt / (2^a.toNat : Int))
      else if b.toInt < 0 then BitVec.ofInt 256 (-1) else 0) = value) :
    Assembly.driverSteps 1 2 #[] (site 3 (a::b::tail)).state =
      .ok (expected (site 3 (a::b::tail)) (value::tail)) := by
  let base : Site .SAR := ⟨seed 3,[.push ⟨1,by decide⟩ #v[0x1d],.op .POP],[.op .STOP],by decide⟩
  have h := (sar_agreement base a b tail room (by change 3 ≤ 3;decide) 0).2.1
  rw [result] at h
  simpa only [base,site,expected,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u] using h

theorem zero_count :
    Assembly.driverSteps 1 2 #[] (site 3 (0::w (-7)::spill)).state =
      .ok (expected (site 3 (0::w (-7)::spill)) (w (-7)::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem negative_odd :
    Assembly.driverSteps 1 2 #[] (site 3 (1::w (-7)::spill)).state =
      .ok (expected (site 3 (1::w (-7)::spill)) (w (-4)::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem positive_odd :
    Assembly.driverSteps 1 2 #[] (site 3 (1::7::spill)).state =
      .ok (expected (site 3 (1::7::spill)) (3::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem last_count :
    Assembly.driverSteps 1 2 #[] (site 3 (255::minimum::spill)).state =
      .ok (expected (site 3 (255::minimum::spill)) (w (-1)::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem exact_saturation :
    Assembly.driverSteps 1 2 #[] (site 3 (256::minimum::spill)).state =
      .ok (expected (site 3 (256::minimum::spill)) (w (-1)::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem over_saturation :
    Assembly.driverSteps 1 2 #[] (site 3 (257::w (-7)::spill)).state =
      .ok (expected (site 3 (257::w (-7)::spill)) (w (-1)::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem maximal_count :
    Assembly.driverSteps 1 2 #[] (site 3 (maximum::w (-7)::spill)).state =
      .ok (expected (site 3 (maximum::w (-7)::spill)) (w (-1)::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem positive_saturation :
    Assembly.driverSteps 1 2 #[] (site 3 (maximum::positiveMaximum::spill)).state =
      .ok (expected (site 3 (maximum::positiveMaximum::spill)) (0::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem minimum_identity :
    Assembly.driverSteps 1 2 #[] (site 3 (0::minimum::spill)).state =
      .ok (expected (site 3 (0::minimum::spill)) (minimum::spill)) := by
  exact execute _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem stack_boundary :
    Assembly.driverSteps 1 2 #[] (site 3 (1::w (-7)::List.replicate 1022 513)).state =
      .ok (expected (site 3 (1::w (-7)::List.replicate 1022 513))
        (w (-4)::List.replicate 1022 513)) := by
  apply execute
  · simp only [List.length_replicate];decide
  · decide +kernel

private def combination : Site .SAR :=
  modularSite ⟨seed 8,[.push ⟨1,by decide⟩ #v[0x1d],.op .POP],[.op .SMOD,.op .STOP],by decide⟩
    (1::w (-7)::3::spill)

theorem fetched_combination :
    Scalar.run [.op .SAR,.op .SMOD] (1::w (-7)::3::spill) = some (w (-1)::spill) ∧
    Assembly.driverSteps 2 3 #[] combination.state =
      .ok {combination.state with
        pc := u 5,gasAvailable := u 0,execLength := 43
        stack := (w (-1)::spill).map (fun x => UInt256.mk x.toFin)} := by
  constructor
  · decide +kernel
  · let base : Site .SAR := ⟨seed 8,[.push ⟨1,by decide⟩ #v[0x1d],.op .POP],[.op .SMOD,.op .STOP],by decide⟩
    have first := (sar_agreement base 1 (w (-7)) (3::spill) (by decide +kernel)
      (by change 3 ≤ 8;decide) 1).2.1
    have result : (if (1 : Scalar.Word).toNat < 256 then
        BitVec.ofInt 256 ((w (-7)).toInt / (2^(1 : Scalar.Word).toNat : Int))
        else if (w (-7)).toInt < 0 then BitVec.ofInt 256 (-1) else 0) = w (-4) := by decide +kernel
    rw [result] at first
    have first' : Assembly.driverSteps 1 3 #[] combination.state =
        .ok ((Assembly.chargedPrepare combination.state 3).replaceStackAndIncrPC
          ((w (-4)::3::spill).map (fun x => UInt256.mk x.toFin))) := by
      simpa only [combination,base] using first
    rw [fetched_steps_cons 1 1 #[] combination.state,first']
    rfl

theorem gas_before_arity :
    Assembly.driverSteps 1 2 #[] (site 2 []).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (site 3 []).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem fuel_refusal :
    Assembly.driverSteps 1 1 #[] (site 3 (1::w (-7)::spill)).state = .error .OutOfFuel := by rfl

theorem wrong_truncation :
    Scalar.step (.op .SAR) (1::w (-7)::spill) ≠ some (w (-3)::spill) := by decide +kernel

theorem wrong_operand_order :
    Scalar.step (.op .SAR) (1::w (-7)::spill) ≠ Scalar.step (.op .SAR) (w (-7)::1::spill) := by decide +kernel

theorem wrong_logical_shift :
    Scalar.step (.op .SAR) (1::w (-7)::spill) ≠ some (((w (-7)) >>> 1)::spill) := by decide +kernel

#print axioms zero_count
#print axioms negative_odd
#print axioms positive_odd
#print axioms last_count
#print axioms exact_saturation
#print axioms over_saturation
#print axioms maximal_count
#print axioms positive_saturation
#print axioms minimum_identity
#print axioms stack_boundary
#print axioms fetched_combination
#print axioms gas_before_arity
#print axioms fuel_refusal
#print axioms wrong_truncation
#print axioms wrong_operand_order
#print axioms wrong_logical_shift
end SolidityBridge.RoadmapV15.P10.ArithmeticShiftControls
