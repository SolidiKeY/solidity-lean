import SolidityBridge.RoadmapV15.P10.SignExtensionPositive

/-! Nonzero truncation clients. The residue sign bit is clear even when the
full input has high bits or is negative under its full-width signed view. -/
namespace SolidityBridge.RoadmapV15.P10.SignExtensionResidueWitness
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
private def next (w : Fin 32) (b value : Scalar.Word) : EVM.State :=
  (Assembly.chargedPrepare (start w b) 5).replaceStackAndIncrPC
    ((value::[258,513]).map (fun x => UInt256.mk x.toFin))
theorem int8_high_bits :
    Scalar.run (Scalar.signedCode ⟨0,by decide⟩) [383,258,513] = some [127,258,513] ∧
    Assembly.driverSteps 1 2 #[] (start ⟨0,by decide⟩ 383) = .ok (next ⟨0,by decide⟩ 383 127) ∧
    EVM.X 2 #[] (start ⟨0,by decide⟩ 383) = EVM.X 1 #[] (next ⟨0,by decide⟩ 383 127) := by
  have h := signextend_nonnegative_residue_agreement site ⟨0,by decide⟩ 383 [258,513]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0
  have cleaned : Scalar.unsignedClean ⟨0,by decide⟩ 383=127 := by decide +kernel
  dsimp only at h ⊢
  rw [cleaned] at h
  exact h

theorem int16_high_bits :
    Scalar.run (Scalar.signedCode ⟨1,by decide⟩) [(2^200+128),258,513] = some [128,258,513] ∧
    Assembly.driverSteps 1 2 #[] (start ⟨1,by decide⟩ (2^200+128)) = .ok (next ⟨1,by decide⟩ (2^200+128) 128) ∧
    EVM.X 2 #[] (start ⟨1,by decide⟩ (2^200+128)) = EVM.X 1 #[] (next ⟨1,by decide⟩ (2^200+128) 128) := by
  have h := signextend_nonnegative_residue_agreement site ⟨1,by decide⟩ (2^200+128) [258,513]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0
  have cleaned : Scalar.unsignedClean ⟨1,by decide⟩ (2^200+128)=128 := by decide +kernel
  dsimp only at h ⊢
  rw [cleaned] at h
  exact h

theorem negative_fullword_client :
    Scalar.run (Scalar.signedCode ⟨0,by decide⟩) [(2^256-129),258,513] = some [127,258,513] ∧
    Assembly.driverSteps 1 2 #[] (start ⟨0,by decide⟩ (2^256-129)) = .ok (next ⟨0,by decide⟩ (2^256-129) 127) ∧
    EVM.X 2 #[] (start ⟨0,by decide⟩ (2^256-129)) = EVM.X 1 #[] (next ⟨0,by decide⟩ (2^256-129) 127) := by
  have h := signextend_nonnegative_residue_agreement site ⟨0,by decide⟩ (2^256-129) [258,513]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0
  have cleaned : Scalar.unsignedClean ⟨0,by decide⟩ (2^256-129)=127 := by decide +kernel
  dsimp only at h ⊢
  rw [cleaned] at h
  exact h

theorem genuine_truncation : ¬((383 : Scalar.Word).toNat<128) ∧
    Scalar.unsignedClean ⟨0,by decide⟩ 383=127 := by decide +kernel

theorem negative_input_view : (2^256-129 : Scalar.Word).toInt = -129 ∧
    Scalar.unsignedClean ⟨0,by decide⟩ (2^256-129)=127 := by decide +kernel

theorem negative_residue_is_not_unsigned : ¬(384%256<128) ∧
    UInt256.signextend (u 0) (u 384) ≠ u 128 := by decide +kernel

theorem ordered_state_observations : (next ⟨0,by decide⟩ 383 127).stack=[u 127,u 258,u 513] ∧
    (next ⟨0,by decide⟩ 383 127).gasAvailable=u 4 ∧
    (next ⟨0,by decide⟩ 383 127).pc=u 4 ∧ (next ⟨0,by decide⟩ 383 127).execLength=42 ∧
    (start ⟨0,by decide⟩ 383).executionEnv.code.data.toList=[0x60,0x0b,0x50,0x0b,0x00] := by decide +kernel

#print axioms int8_high_bits
#print axioms int16_high_bits
#print axioms negative_fullword_client
#print axioms genuine_truncation
#print axioms negative_input_view
#print axioms negative_residue_is_not_unsigned
#print axioms ordered_state_observations
end SolidityBridge.RoadmapV15.P10.SignExtensionResidueWitness
