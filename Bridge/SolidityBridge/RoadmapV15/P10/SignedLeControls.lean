import SolidityBridge.RoadmapV15.P10.SignedLeFixtures

/-! Actual selected signed <= on inhabited signed inputs and complete States.
Unsigned/strict comparison substitutions and omission of ISZERO are negative controls. -/
namespace SolidityBridge.RoadmapV15.P10.SignedLeControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SignedLeFixtures
open WordPushFixtures (seed before after spill u)

private theorem execute (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 4 #[] (input 6 false a b tail) =
      .ok (observed 6 false a b tail (Scalar.flag (decide (a.toInt ≤ b.toInt)))) := by
  have h := (signed_le_execution (seed 6 false) before after a b tail fits room (by decide) 1).2.1
  simpa only [input,observed,seed,before,after,u,signedLeInput,signedLeCompared,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem typed_client (a b : PrimTy.int.Denote) :
    Scalar.run Scalar.intLe.code (Scalar.encodeValue .int a::Scalar.encodeValue .int b::spill) =
      (BinOp.le.evalT (p := .int) rfl a b).map (fun r => Scalar.encodeValue .bool r::spill) ∧
    Assembly.driverSteps 2 4 #[] (input 12 true (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill) =
      .ok (observed 12 true (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill (Scalar.flag (decide (a.val ≤ b.val)))) ∧
    EVM.X 4 #[] (input 12 true (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill) =
      EVM.X 2 #[] (observed 12 true (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill (Scalar.flag (decide (a.val ≤ b.val)))) := by
  have h := selected_signed_le_execution (seed 12 true) before after a b spill fits (by decide) (by decide) 1
  dsimp only at h
  simp only [Scalar.encode_int_toInt] at h
  simpa only [input,observed,seed,before,after,u,signedLeInput,signedLeCompared,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem typed_signed_cases :
    (Scalar.run Scalar.intLe.code (w (-1)::0::spill) = some (1::spill) ∧
    Assembly.driverSteps 2 4 #[] (input 12 true (w (-1)) 0 spill) = .ok (observed 12 true (w (-1)) 0 spill 1) ∧
    EVM.X 4 #[] (input 12 true (w (-1)) 0 spill) = EVM.X 2 #[] (observed 12 true (w (-1)) 0 spill 1)) ∧
    (Scalar.run Scalar.intLe.code (0::w (-1)::spill) = some (0::spill) ∧
    Assembly.driverSteps 2 4 #[] (input 12 true 0 (w (-1)) spill) = .ok (observed 12 true 0 (w (-1)) spill 0) ∧
    EVM.X 4 #[] (input 12 true 0 (w (-1)) spill) = EVM.X 2 #[] (observed 12 true 0 (w (-1)) spill 0)) := by
  exact ⟨typed_client ⟨-1,by decide⟩ ⟨0,by decide⟩,typed_client ⟨0,by decide⟩ ⟨-1,by decide⟩⟩

theorem boundaries_and_equality :
    Assembly.driverSteps 2 4 #[] (input 6 false (w (-(2^255))) (w (2^255-1)) spill) =
      .ok (observed 6 false (w (-(2^255))) (w (2^255-1)) spill 1) ∧
    Assembly.driverSteps 2 4 #[] (input 6 false (w (2^255-1)) (w (-(2^255))) spill) =
      .ok (observed 6 false (w (2^255-1)) (w (-(2^255))) spill 0) ∧
    Assembly.driverSteps 2 4 #[] (input 6 false 7 7 spill) = .ok (observed 6 false 7 7 spill 1) := by
  have power : (2^255 : Int) = ((2^255 : Nat) : Int) := (Nat.cast_pow 2 255).symm
  simp only [power]
  have low : (w (-((2^255 : Nat) : Int))).toInt = -((2^255 : Nat) : Int) :=
    Scalar.encode_int_toInt ⟨-((2^255 : Nat) : Int),by decide⟩
  have high : (w (((2^255 : Nat) : Int)-1)).toInt = ((2^255 : Nat) : Int)-1 :=
    Scalar.encode_int_toInt ⟨((2^255 : Nat) : Int)-1,by decide⟩
  have forward := execute (w (-((2^255 : Nat) : Int))) (w (((2^255 : Nat) : Int)-1)) spill (by decide)
  have backward := execute (w (((2^255 : Nat) : Int)-1)) (w (-((2^255 : Nat) : Int))) spill (by decide)
  rw [low,high] at forward backward
  have yes : Scalar.flag (decide (-((2^255 : Nat) : Int) ≤ ((2^255 : Nat) : Int)-1)) = 1 := by decide
  have no : Scalar.flag (decide (((2^255 : Nat) : Int)-1 ≤ -((2^255 : Nat) : Int))) = 0 := by decide
  rw [yes] at forward
  rw [no] at backward
  exact ⟨forward,backward,execute 7 7 spill (by decide)⟩

theorem full_input_stack :
    Assembly.driverSteps 2 4 #[] (input 6 false (w (-1)) 0 (List.replicate 1022 769)) =
      .ok (observed 6 false (w (-1)) 0 (List.replicate 1022 769) 1) := by
  exact execute _ _ _ (by simp only [List.length_replicate];decide)

theorem refused_resources :
    Assembly.driverSteps 2 3 #[] (input 2 false (w (-1)) 0 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 2 3 #[] (input 5 false (w (-1)) 0 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 2 2 #[] (input 6 false (w (-1)) 0 spill) = .error .OutOfFuel ∧
    Assembly.driverSteps 2 3 #[] (signedLeInput (seed 3 false) before after [7]) = .error .StackUnderflow ∧
    Assembly.driverSteps 2 3 #[] (signedLeInput (seed 2 false) before after [7]) = .error .OutOfGass := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩


theorem values_and_ordered_observations :
    Scalar.run [.op .SGT] (w (-1)::0::spill) ≠ some (1::spill) ∧
    UInt256.gt ⟨(w (-1)).toFin⟩ (u 0) ≠ UInt256.sgt ⟨(w (-1)).toFin⟩ (u 0) ∧
    (BinOp.le.evalT (p := .int) rfl ⟨7,by decide⟩ ⟨7,by decide⟩) = some true ∧
    (BinOp.lt.evalT (p := .int) rfl ⟨7,by decide⟩ ⟨7,by decide⟩) = some false ∧
    (input 6 false (w (-1)) 0 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x13,0x15,0x00] ∧
    (signedLeCompared (seed 6 false) before after (w (-1)) 0 spill).stack = [u 0,u 258,u 513] ∧
    (signedLeCompared (seed 6 false) before after (w (-1)) 0 spill).gasAvailable.toNat = 3 ∧
    (signedLeCompared (seed 6 false) before after (w (-1)) 0 spill).pc.toNat = 4 ∧
    (signedLeCompared (seed 6 false) before after (w (-1)) 0 spill).execLength = 42 ∧
    (observed 6 false (w (-1)) 0 spill 1).stack = [u 1,u 258,u 513] ∧
    (observed 6 false (w (-1)) 0 spill 1).gasAvailable.toNat = 0 ∧
    (observed 6 false (w (-1)) 0 spill 1).pc.toNat = 5 ∧
    (observed 6 false (w (-1)) 0 spill 1).execLength = 43 ∧
    (observed 6 false (w (-1)) 0 spill 1).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
    (observed 6 false (w (-1)) 0 spill 1).returnData.data.toList = [0xcc,0xdd] ∧
    (observed 6 false (w (-1)) 0 spill 1).H_return.data.toList = [0xee,0xff] ∧
    (observed 6 false (w (-1)) 0 spill 1).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide


#print axioms typed_client
#print axioms typed_signed_cases
#print axioms boundaries_and_equality
#print axioms full_input_stack
#print axioms refused_resources
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.SignedLeControls
