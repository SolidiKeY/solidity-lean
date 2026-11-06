import SolidityBridge.RoadmapV15.P10.SignExtensionPositive

/-! Nonzero clients of the new positive-range producer. Negative and truncating
inputs stay outside this theorem and remain obligations of the full row. -/
namespace SolidityBridge.RoadmapV15.P10.SignExtensionPositiveWitness
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def seed : EVM.State :=
  {(default : EVM.State) with
    gasAvailable := u 9,execLength := 41,activeWords := u 3,stack := [u 258,u 513]
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := false
      calldata := ⟨#[0x11,0x22,0x33]⟩}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
private def site : Site .SIGNEXTEND :=
  ⟨seed,[.push ⟨1,by decide⟩ #v[0x0b],.op .POP],[.op .STOP],by decide⟩
private def start (w : Fin 32) (b : Scalar.Word) : EVM.State :=
  (modularSite site (BitVec.ofNat 256 w.val::b::[258,513])).state
private def next (w : Fin 32) (b : Scalar.Word) : EVM.State :=
  (Assembly.chargedPrepare (start w b) 5).replaceStackAndIncrPC
    ((b::[258,513]).map (fun x => UInt256.mk x.toFin))
theorem int8_positive_boundary :
    Scalar.run (Scalar.signedCode ⟨0,by decide⟩) [127,258,513] = some [127,258,513] ∧
    Assembly.driverSteps 1 2 #[] (start ⟨0,by decide⟩ 127) = .ok (next ⟨0,by decide⟩ 127) ∧
    EVM.X 2 #[] (start ⟨0,by decide⟩ 127) = EVM.X 1 #[] (next ⟨0,by decide⟩ 127) := by
  exact signextend_positive_agreement site ⟨0,by decide⟩ 127 [258,513]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0

theorem int16_nonzero :
    Scalar.run (Scalar.signedCode ⟨1,by decide⟩) [128,258,513] = some [128,258,513] ∧
    Assembly.driverSteps 1 2 #[] (start ⟨1,by decide⟩ 128) = .ok (next ⟨1,by decide⟩ 128) ∧
    EVM.X 2 #[] (start ⟨1,by decide⟩ 128) = EVM.X 1 #[] (next ⟨1,by decide⟩ 128) := by
  exact signextend_positive_agreement site ⟨1,by decide⟩ 128 [258,513]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0

theorem int256_positive_boundary :
    Scalar.run (Scalar.signedCode ⟨31,by decide⟩) [(2^255-1),258,513] = some [(2^255-1),258,513] ∧
    Assembly.driverSteps 1 2 #[] (start ⟨31,by decide⟩ (2^255-1)) = .ok (next ⟨31,by decide⟩ (2^255-1)) ∧
    EVM.X 2 #[] (start ⟨31,by decide⟩ (2^255-1)) = EVM.X 1 #[] (next ⟨31,by decide⟩ (2^255-1)) := by
  exact signextend_positive_agreement site ⟨31,by decide⟩ (2^255-1) [258,513]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0

theorem strict_bound_is_necessary : ¬(128<2^(0*8+7)) ∧
    UInt256.signextend (u 0) (u 128) ≠ u 128 := by decide +kernel

theorem byte_index_is_necessary :
    UInt256.signextend (u 0) (u 128) ≠ UInt256.signextend (u 1) (u 128) := by decide +kernel

theorem ordered_state_observations : (next ⟨0,by decide⟩ 127).gasAvailable = u 4 ∧
    (next ⟨0,by decide⟩ 127).pc=u 4 ∧ (next ⟨0,by decide⟩ 127).execLength=42 ∧
    (start ⟨0,by decide⟩ 127).executionEnv.code.data.toList=[0x60,0x0b,0x50,0x0b,0x00] := by decide +kernel

#print axioms int8_positive_boundary
#print axioms int16_nonzero
#print axioms int256_positive_boundary
#print axioms strict_bound_is_necessary
#print axioms byte_index_is_necessary
#print axioms ordered_state_observations
end SolidityBridge.RoadmapV15.P10.SignExtensionPositiveWitness
