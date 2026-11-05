import SolidityBridge.RoadmapV15.P10.SignExtensionPositive

/-! Unified all-index/all-sign clients of the actual Scalar/reference producer.
Full source/compiler-origin and approved Osaka correspondence remain separate. -/
namespace SolidityBridge.RoadmapV15.P10.SignExtensionAllWitness
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
private def start (a b : Scalar.Word) : EVM.State :=
  (modularSite site (a::b::[258,513])).state
private def next (a b value : Scalar.Word) : EVM.State :=
  (Assembly.chargedPrepare (start a b) 5).replaceStackAndIncrPC
    ((value::[258,513]).map (fun x => UInt256.mk x.toFin))
theorem byte_negative :
    Scalar.step (.op .SIGNEXTEND) [0,128,258,513]=some [(BitVec.ofInt 256 (-128)),258,513] ∧
    Assembly.driverSteps 1 2 #[] (start 0 128)=.ok (next 0 128 (BitVec.ofInt 256 (-128))) ∧
    EVM.X 2 #[] (start 0 128)=EVM.X 1 #[] (next 0 128 (BitVec.ofInt 256 (-128))) := by
  have h := signextend_all_agreement site 0 128 [258,513]
    (by decide +kernel) (by decide +kernel) 0
  have result : (if h : (0 : Scalar.Word).toNat<32 then
    Scalar.signedClean ⟨(0 : Scalar.Word).toNat,h⟩ 128 else 128)=(BitVec.ofInt 256 (-128)) := by decide +kernel
  dsimp only at h ⊢
  rw [result] at h
  exact h

theorem byte_truncating :
    Scalar.step (.op .SIGNEXTEND) [0,384,258,513]=some [(BitVec.ofInt 256 (-128)),258,513] ∧
    Assembly.driverSteps 1 2 #[] (start 0 384)=.ok (next 0 384 (BitVec.ofInt 256 (-128))) ∧
    EVM.X 2 #[] (start 0 384)=EVM.X 1 #[] (next 0 384 (BitVec.ofInt 256 (-128))) := by
  have h := signextend_all_agreement site 0 384 [258,513]
    (by decide +kernel) (by decide +kernel) 0
  have result : (if h : (0 : Scalar.Word).toNat<32 then
    Scalar.signedClean ⟨(0 : Scalar.Word).toNat,h⟩ 384 else 384)=(BitVec.ofInt 256 (-128)) := by decide +kernel
  dsimp only at h ⊢
  rw [result] at h
  exact h

theorem two_byte_high_negative :
    Scalar.step (.op .SIGNEXTEND) [1,(2^200+32768),258,513]=some [(BitVec.ofInt 256 (-32768)),258,513] ∧
    Assembly.driverSteps 1 2 #[] (start 1 (2^200+32768))=.ok (next 1 (2^200+32768) (BitVec.ofInt 256 (-32768))) ∧
    EVM.X 2 #[] (start 1 (2^200+32768))=EVM.X 1 #[] (next 1 (2^200+32768) (BitVec.ofInt 256 (-32768))) := by
  have h := signextend_all_agreement site 1 (2^200+32768) [258,513]
    (by decide +kernel) (by decide +kernel) 0
  have result : (if h : (1 : Scalar.Word).toNat<32 then
    Scalar.signedClean ⟨(1 : Scalar.Word).toNat,h⟩ (2^200+32768) else (2^200+32768))=(BitVec.ofInt 256 (-32768)) := by decide +kernel
  dsimp only at h ⊢
  rw [result] at h
  exact h

theorem fullwidth_minimum :
    Scalar.step (.op .SIGNEXTEND) [31,(2^255),258,513]=some [(2^255),258,513] ∧
    Assembly.driverSteps 1 2 #[] (start 31 (2^255))=.ok (next 31 (2^255) (2^255)) ∧
    EVM.X 2 #[] (start 31 (2^255))=EVM.X 1 #[] (next 31 (2^255) (2^255)) := by
  have h := signextend_all_agreement site 31 (2^255) [258,513]
    (by decide +kernel) (by decide +kernel) 0
  have result : (if h : (31 : Scalar.Word).toNat<32 then
    Scalar.signedClean ⟨(31 : Scalar.Word).toNat,h⟩ (2^255) else (2^255))=(2^255) := by decide +kernel
  dsimp only at h ⊢
  rw [result] at h
  exact h

theorem first_large_index :
    Scalar.step (.op .SIGNEXTEND) [32,128,258,513]=some [128,258,513] ∧
    Assembly.driverSteps 1 2 #[] (start 32 128)=.ok (next 32 128 128) ∧
    EVM.X 2 #[] (start 32 128)=EVM.X 1 #[] (next 32 128 128) := by
  have h := signextend_all_agreement site 32 128 [258,513]
    (by decide +kernel) (by decide +kernel) 0
  have result : (if h : (32 : Scalar.Word).toNat<32 then
    Scalar.signedClean ⟨(32 : Scalar.Word).toNat,h⟩ 128 else 128)=128 := by decide +kernel
  dsimp only at h ⊢
  rw [result] at h
  exact h

theorem max_index_max_value :
    Scalar.step (.op .SIGNEXTEND) [(2^256-1),(2^256-1),258,513]=some [(2^256-1),258,513] ∧
    Assembly.driverSteps 1 2 #[] (start (2^256-1) (2^256-1))=.ok (next (2^256-1) (2^256-1) (2^256-1)) ∧
    EVM.X 2 #[] (start (2^256-1) (2^256-1))=EVM.X 1 #[] (next (2^256-1) (2^256-1) (2^256-1)) := by
  have h := signextend_all_agreement site (2^256-1) (2^256-1) [258,513]
    (by decide +kernel) (by decide +kernel) 0
  have result : (if h : ((2^256-1) : Scalar.Word).toNat<32 then
    Scalar.signedClean ⟨((2^256-1) : Scalar.Word).toNat,h⟩ (2^256-1) else (2^256-1))=(2^256-1) := by decide +kernel
  dsimp only at h ⊢
  rw [result] at h
  exact h

theorem wrong_unsigned_step : Assembly.driverSteps 1 2 #[] (start 0 384) ≠ .ok (next 0 384 128) := by
  rw [byte_truncating.2.1]
  intro h
  have top := congrArg (fun o => o.toOption.map (·.stack.head?)) h
  change some (some (UInt256.mk (BitVec.ofInt 256 (-128)).toFin)) =
    some (some (UInt256.mk (128 : Scalar.Word).toFin)) at top
  exact (by decide +kernel : UInt256.mk (BitVec.ofInt 256 (-128)).toFin ≠
    UInt256.mk (128 : Scalar.Word).toFin) (Option.some.inj (Option.some.inj top))

theorem wrong_index_wrap : Assembly.driverSteps 1 2 #[] (start 32 128) ≠
    .ok (next 32 128 (BitVec.ofInt 256 (-128))) := by
  rw [first_large_index.2.1]
  intro h
  have top := congrArg (fun o => o.toOption.map (·.stack.head?)) h
  change some (some (UInt256.mk (128 : Scalar.Word).toFin)) =
    some (some (UInt256.mk (BitVec.ofInt 256 (-128)).toFin)) at top
  exact (by decide +kernel : UInt256.mk (128 : Scalar.Word).toFin ≠
    UInt256.mk (BitVec.ofInt 256 (-128)).toFin) (Option.some.inj (Option.some.inj top))

theorem negative_views : (Scalar.signedClean ⟨0,by decide⟩ 384).toInt = -128 ∧
    (Scalar.signedClean ⟨31,by decide⟩ (2^255)).toInt = -(2^255 : Int) := by decide +kernel

theorem ordered_state_observations : (next 0 384 (BitVec.ofInt 256 (-128))).stack=
    [u (2^256-128),u 258,u 513] ∧
    (next 0 384 (BitVec.ofInt 256 (-128))).gasAvailable=u 4 ∧
    (next 0 384 (BitVec.ofInt 256 (-128))).pc=u 4 ∧
    (next 0 384 (BitVec.ofInt 256 (-128))).execLength=42 ∧
    (start 0 384).executionEnv.code.data.toList=[0x60,0x0b,0x50,0x0b,0x00] := by decide +kernel

#print axioms byte_negative
#print axioms byte_truncating
#print axioms two_byte_high_negative
#print axioms fullwidth_minimum
#print axioms first_large_index
#print axioms max_index_max_value
#print axioms wrong_unsigned_step
#print axioms wrong_index_wrap
#print axioms negative_views
#print axioms ordered_state_observations
end SolidityBridge.RoadmapV15.P10.SignExtensionAllWitness
