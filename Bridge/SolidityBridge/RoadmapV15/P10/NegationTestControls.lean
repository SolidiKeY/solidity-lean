import SolidityBridge.RoadmapV15.P10.NegationTest
import SolidityBridge.RoadmapV15.P10.NegationBodyControls

/-! Exact complete States of the real negation test; no branch/panic execution. -/
namespace SolidityBridge.RoadmapV15.P10.NegationTestControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External WordPushFixtures
open NegationBodyControls

private theorem fits : (Backend.encode (before ++ [negationDup,
    Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt)])).length < UInt256.size := by decide

def expected (perm flag : Bool) (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  {negationTestInput (seed 9 perm) before after a tail with
    pc := u 38,gasAvailable := u 0,execLength := 44
    stack := (Scalar.flag flag::Scalar.encodeValue .int a::tail).map (fun w => UInt256.mk w.toFin)}

theorem exact_budget (perm : Bool) (a : PrimTy.int.Denote) (tail : Scalar.Stack)
    (room : tail.length+3 ≤ 1024) :
    Assembly.driverSteps 3 4 #[] (negationTestInput (seed 9 perm) before after a tail) =
      .ok (expected perm (!PrimTy.int.inRange (-a.val)) a tail) := by
  have h := (negation_test_execution (seed 9 perm) before after a tail fits room
    (by change 9 ≤ 9;decide) 0).2.1
  have gasEq : (negationTestOutput (seed 9 perm) before after a tail).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact negation_test_debit (seed 9 perm) before after a tail (by change 9 ≤ 9;decide)
  have same : negationTestOutput (seed 9 perm) before after a tail =
      expected perm (!PrimTy.int.inRange (-a.val)) a tail := by
    change ({negationTestInput (seed 9 perm) before after a tail with
      pc := u 38,gasAvailable := (negationTestOutput (seed 9 perm) before after a tail).gasAvailable,
      execLength := 44,stack := (Scalar.flag (!PrimTy.int.inRange (-a.val))::
        Scalar.encodeValue .int a::tail).map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
    rw [gasEq]
    rfl
  exact h.trans (congrArg Except.ok same)

theorem ordinary_and_minimum :
    Assembly.driverSteps 3 4 #[] (negationTestInput (seed 9 false) before after negative spill) =
      .ok (expected false false negative spill) ∧
    Assembly.driverSteps 3 4 #[] (negationTestInput (seed 9 true) before after zero spill) =
      .ok (expected true false zero spill) ∧
    Assembly.driverSteps 3 4 #[] (negationTestInput (seed 9 true) before after Scalar.minimumInt spill) =
      .ok (expected true true Scalar.minimumInt spill) := by
  exact ⟨exact_budget false negative spill (by decide),exact_budget true zero spill (by decide),
    exact_budget true Scalar.minimumInt spill (by decide)⟩

theorem capacity_boundary :
    Assembly.driverSteps 3 4 #[]
      (negationTestInput (seed 9 false) before after positive (List.replicate 1021 9)) =
      .ok (expected false false positive (List.replicate 1021 9)) ∧
    Assembly.driverSteps 3 4 #[] (negationTestInput (seed 9 true) before after maximum []) =
      .ok (expected true false maximum []) := by
  exact ⟨exact_budget false positive (List.replicate 1021 9)
    (by simp only [List.length_replicate];omega),exact_budget true maximum [] (by decide)⟩

theorem refusals :
    Assembly.driverSteps 3 3 #[] (negationTestInput (seed 9 false) before after negative spill) =
      .error .OutOfFuel ∧
    Assembly.driverSteps 3 4 #[] (negationTestInput (seed 8 true) before after Scalar.minimumInt spill) =
      .error .OutOfGass ∧
    Assembly.driverSteps 3 4 #[]
      (negationTestInput (seed 9 false) before after negative (List.replicate 1022 9)) =
      .error .StackOverflow := by
  refine ⟨?_,?_,?_⟩
  · rfl
  · rfl
  · exact negation_test_overflow (seed 9 false) before after negative (List.replicate 1022 9)
      (by decide) (by simp only [List.length_replicate]) (by decide)

theorem ordered_observation :
    (expected true true Scalar.minimumInt spill).executionEnv.code.data.toList =
      [0x60,0x7f,0x50,0x80,0x7f,0x80] ++ List.replicate 31 0 ++ [0x14,0x00] ∧
    (expected false false negative spill).stack =
      [u 0,UInt256.mk (Scalar.encodeValue .int negative).toFin,u 258,u 513] ∧
    (expected true true Scalar.minimumInt spill).stack ≠
      [u 0,UInt256.mk (Scalar.encodeValue .int Scalar.minimumInt).toFin,u 258,u 513] ∧
    (expected true true Scalar.minimumInt spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected true true Scalar.minimumInt spill).H_return.data.toList = [0xee,0xff] ∧
    (expected true true Scalar.minimumInt spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected true true Scalar.minimumInt spill).memory = (seed 9 true).memory ∧
    (expected true true Scalar.minimumInt spill).accountMap = accounts ∧
    (expected true true Scalar.minimumInt spill).σ₀ = accounts ∧
    (expected true true Scalar.minimumInt spill).substate = (seed 9 true).substate := by
  exact ⟨by decide,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms exact_budget
#print axioms ordinary_and_minimum
#print axioms capacity_boundary
#print axioms refusals
#print axioms ordered_observation
end SolidityBridge.RoadmapV15.P10.NegationTestControls
