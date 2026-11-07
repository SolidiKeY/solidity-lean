import SolidityBridge.PrecompileAgreement.Identity
import SolidityBridge.PrecompileAgreement.Header

/-! Inhabited inputs, malformed and gas-boundary controls. Native FFI outputs
remain open. In particular a kernel stub success is not native curve validity. -/
namespace SolidityBridge.PrecompileAgreement.Controls
open Solidity Solidity.Precompiles Solidity.Roadmap.Evm EvmYul

def array (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩
def filled (n : Nat) : ByteArray := ⟨Array.replicate n 0xa5⟩
def zeros (n : Nat) : Bytes := List.replicate n 0
def input (d : ByteArray) : ExecutionEnv .EVM := {(default : ExecutionEnv .EVM) with calldata := d}
def lengths : List Nat := [0,1,31,32,33,63,64,65]

theorem identity_lengths : lengths.map (fun n => identityGas (filled n).toList) =
    [15,18,18,18,21,21,21,24] := by
  simp only [lengths, List.map_cons, List.map_nil, identity_gas, filled, ByteArray.size,
    Array.size_replicate]

theorem sha_lengths : lengths.map (fun n => Osaka.gas .sha256 (filled n).toList) =
    [60,72,72,72,84,84,84,96] := by
  simp only [lengths, List.map_cons, List.map_nil, sha_price, filled, ByteArray.size,
    Array.size_replicate]

theorem ripemd_lengths : lengths.map (fun n => Osaka.gas .ripemd160 (filled n).toList) =
    [600,720,720,720,840,840,840,960] := by
  simp only [lengths, List.map_cons, List.map_nil, ripemd_price, filled, ByteArray.size,
    Array.size_replicate]

theorem identity_nonzero_output :
    (Ξ_ID default (UInt256.ofNat 18) default (input (array [0,128,255,1]))).2.2.2.2 =
      array [0,128,255,1] := rfl

theorem identity_boundary :
    (Ξ_ID default (UInt256.ofNat 17) default (input (array [0,128,255,1]))).1 = false ∧
    (Ξ_ID default (UInt256.ofNat 18) default (input (array [0,128,255,1]))).1 = true ∧
    (Ξ_ID default (UInt256.ofNat 19) default (input (array [0,128,255,1]))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem sha_boundary :
    (Ξ_SHA256 default (UInt256.ofNat 71) default (input (array [97,98,99]))).1 = false ∧
    (Ξ_SHA256 default (UInt256.ofNat 72) default (input (array [97,98,99]))).1 = true ∧
    (Ξ_SHA256 default (UInt256.ofNat 73) default (input (array [97,98,99]))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem ripemd_boundary :
    (Ξ_RIP160 default (UInt256.ofNat 719) default (input (array [97,98,99]))).1 = false ∧
    (Ξ_RIP160 default (UInt256.ofNat 720) default (input (array [97,98,99]))).1 = true ∧
    (Ξ_RIP160 default (UInt256.ofNat 721) default (input (array [97,98,99]))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

def invalid_recovery : Bytes := zeros 32 ++ word 29 ++ zeros 64

theorem ecrecover_controls : ecrecover invalid_recovery = some [] ∧
    (Ξ_ECREC default (UInt256.ofNat 2999) default (input (array invalid_recovery))).1 = false ∧
    (Ξ_ECREC default (UInt256.ofNat 3000) default (input (array invalid_recovery))).1 = true ∧
    (Ξ_ECREC default (UInt256.ofNat 3001) default (input (array invalid_recovery))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

def bad_point : Bytes := word Bn254.p ++ zeros 96

theorem bnadd_controls :
    ([127,128,129].map (fun n => (Bn254.add (zeros n)).isSome)) = [true,true,true] ∧
    (Bn254.add bad_point).isNone = true ∧
    (Ξ_BN_ADD default (UInt256.ofNat 149) default (input (array (zeros 128)))).1 = false ∧
    (Ξ_BN_ADD default (UInt256.ofNat 150) default (input (array (zeros 128)))).1 = true ∧
    (Ξ_BN_ADD default (UInt256.ofNat 151) default (input (array (zeros 128)))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem bnmul_controls :
    ([95,96,97].map (fun n => (Bn254.mul (zeros n)).isSome)) = [true,true,true] ∧
    (Bn254.mul (bad_point.take 96)).isNone = true ∧
    (Ξ_BN_MUL default (UInt256.ofNat 5999) default (input (array (zeros 96)))).1 = false ∧
    (Ξ_BN_MUL default (UInt256.ofNat 6000) default (input (array (zeros 96)))).1 = true ∧
    (Ξ_BN_MUL default (UInt256.ofNat 6001) default (input (array (zeros 96)))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem pairing_controls :
    ([0,1,191,192,193,383,384,385].map (fun n => (Bn254.pairing (zeros n)).isNone)) =
      [false,true,true,false,true,true,false,true] ∧
    (Ξ_SNARKV default (UInt256.ofNat 78999) default (input (array (zeros 192)))).1 = false ∧
    (Ξ_SNARKV default (UInt256.ofNat 79000) default (input (array (zeros 192)))).1 = true ∧
    (Ξ_SNARKV default (UInt256.ofNat 79001) default (input (array (zeros 192)))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

def blake_one : ByteArray := array ([0,0,0,1] ++ zeros 209)
def blake_bad_flag : ByteArray := array ([0,0,0,1] ++ zeros 208 ++ [2])

theorem blake_controls : Osaka.gas .blake2f blake_one.toList = 1 ∧
    (Blake2f.blake2f blake_one.toList).isSome = true ∧
    (Blake2f.blake2f blake_bad_flag.toList).isNone = true ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 0) default (input blake_one)).1 = false ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 1) default (input blake_one)).1 = true ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 2) default (input blake_one)).2.2.1.toNat = 1 ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 2) default (input blake_bad_flag)).1 = false ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 2) default (input blake_bad_flag)).2.2.1.toNat = 0 := by
  have header : fromByteArrayBigEndian (blake_one.extract 0 4) = 1 := by
    rw [← blake_price blake_one (by decide +kernel), byte_list]
    decide +kernel
  have sz : blake_one.size = 213 := by decide +kernel
  have flag : blake_one[212]! = 0 := by decide +kernel
  have badsz : blake_bad_flag.size = 213 := by decide +kernel
  have badflag : blake_bad_flag[212]! = 2 := by decide +kernel
  have core : Osaka.gas .blake2f blake_one.toList = 1 ∧
      (Blake2f.blake2f blake_one.toList).isSome = true ∧
      (Blake2f.blake2f blake_bad_flag.toList).isNone = true := by
    repeat' apply And.intro
    all_goals rw [byte_list]
    all_goals decide +kernel
  generalize blake_one = d at header sz flag core ⊢
  generalize blake_bad_flag = e at badsz badflag core ⊢
  repeat' apply And.intro
  · exact core.1
  · exact core.2.1
  · exact core.2.2
  · exact congrArg Prod.fst (blake_insufficient default (UInt256.ofNat 0) default (input d)
      (by change 0 < fromByteArrayBigEndian (d.extract 0 4); rw [header]; decide))
  · exact congrArg Prod.fst (blake_valid default (UInt256.ofNat 1) default (input d)
      (by change fromByteArrayBigEndian (d.extract 0 4) ≤ 1; rw [header]) sz flag)
  · have run := blake_valid default (UInt256.ofNat 2) default (input d)
      (by change fromByteArrayBigEndian (d.extract 0 4) ≤ 2; rw [header]; decide) sz flag
    have gas := congrArg (fun r => r.2.2.1.toNat) run
    change _ = (UInt256.ofNat 2 - UInt256.ofNat (fromByteArrayBigEndian (d.extract 0 4))).toNat at gas
    rw [header] at gas
    exact gas
  · exact congrArg Prod.fst (blake_invalid_flag default (UInt256.ofNat 2) default
      (input e) badsz badflag)
  · exact congrArg (fun r => r.2.2.1.toNat) (blake_invalid_flag default (UInt256.ofNat 2) default
      (input e) badsz badflag)


theorem blake_short_mismatch : Osaka.gas .blake2f (array [1]).toList = 16777216 ∧
    fromByteArrayBigEndian ((array [1]).extract 0 4) = 1 ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 1) default (input (array [1]))).1 = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [byte_list]; decide +kernel
  · simp only [fromByteArrayBigEndian, byte_list]; decide +kernel
  · exact congrArg Prod.fst (blake_invalid_size default (UInt256.ofNat 1) default
      (input (array [1])) (by decide +kernel))

theorem blake_byte_order : Osaka.gas .blake2f (array [1,2,3,4]).toList = 16909060 ∧
    fromByteArrayBigEndian ((array [1,2,3,4]).extract 0 4) = 16909060 := by
  constructor
  · rw [byte_list]; decide +kernel
  · simp only [fromByteArrayBigEndian, byte_list]; decide +kernel


theorem point_controls : ([0,191,192,193].map (fun n => (PointEval.pointEval (zeros n)).isNone)) =
    [true,true,true,true] ∧
    (Ξ_PointEval default (UInt256.ofNat 49999) default (input (array (zeros 192)))).1 = false ∧
    (Ξ_PointEval default (UInt256.ofNat 50000) default (input (array (zeros 192)))).1 = true ∧
    (Ξ_PointEval default (UInt256.ofNat 50001) default (input (array (zeros 192)))).2.2.1.toNat = 1 := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- This records the vendor's logical subprocess stub; no native-validity
or cryptographic equality follows from its successful flag. -/
theorem ffi_logical_mismatch : (Bn254.add bad_point).isNone = true ∧
    (Ξ_BN_ADD default (UInt256.ofNat 150) default (input (array bad_point))).1 = true ∧
    (PointEval.pointEval (zeros 192)).isNone = true ∧
    (Ξ_PointEval default (UInt256.ofNat 50000) default (input (array (zeros 192)))).1 = true := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem modexp_empty_mismatch : Modexp.gas [] = 500 ∧
    (Ξ_EXPMOD default (UInt256.ofNat 200) default (input (array []))).1 = true ∧
    (Ξ_EXPMOD default (UInt256.ofNat 200) default (input (array []))).2.2.1.toNat = 0 := by
  refine ⟨by decide +kernel, ?_⟩
  constructor
  all_goals simp only [Ξ_EXPMOD, input, nat_of_slice, fromByteArrayBigEndian, byte_list]
  all_goals decide +kernel

def oversized_modexp : Bytes := zeros 30 ++ [4,1] ++ zeros 64

theorem modexp_bound_mismatch : (Modexp.modexp oversized_modexp).isNone = true ∧
    Modexp.gas oversized_modexp = 0 ∧
    (Ξ_EXPMOD default (UInt256.ofNat 6000) default (input (array oversized_modexp))).1 = true ∧
    (Ξ_EXPMOD default (UInt256.ofNat 6000) default (input (array oversized_modexp))).2.2.1.toNat = 453 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  all_goals simp only [Ξ_EXPMOD, input, nat_of_slice, fromByteArrayBigEndian, byte_list]
  all_goals decide +kernel

def unsupported : List Precompile := [.blsG1Add,.blsG1Msm,.blsG2Add,.blsG2Msm,
  .blsPairing,.blsMapFpToG1,.blsMapFp2ToG2,.p256Verify]

theorem unsupported_core : unsupported.map (fun p => (Osaka.run p []).isNone) =
    [true,true,true,true,true,true,true,false] ∧
    unsupported.map (fun p => Osaka.gas p []) = [375,0,600,0,37700,5500,23800,6900] := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- Every malformed size in the planned boundary classes fails the actual
vendor wrapper and consumes the entire supplied gas, for arbitrary states. -/
theorem blake_malformed_lengths (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (n : Nat) (member : n ∈ [0,1,2,3,4,212,214]) :
    Ξ_BLAKE2_F σ g A (input (filled n)) = (false, ∅, ⟨0⟩, A, .empty) := by
  apply blake_invalid_size
  change (filled n).size ≠ 213
  simp only [filled, ByteArray.size, Array.size_replicate]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  omega

theorem blake_core_lengths :
    [0,1,2,3,4,212,213,214].map (fun n => (Blake2f.blake2f (zeros n)).isSome) =
      [false,false,false,false,false,false,true,false] := by decide +kernel

def blake_final_one : ByteArray := array (zeros 212 ++ [1])

theorem blake_final_one_control :
    (Blake2f.blake2f blake_final_one.toList).isSome = true ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 1) default (input blake_final_one)).1 = true := by
  have core : (Blake2f.blake2f blake_final_one.toList).isSome = true := by
    rw [byte_list]; decide +kernel
  have sz : blake_final_one.size = 213 := by decide +kernel
  have flag : blake_final_one[212]! = 1 := by decide +kernel
  have header : fromByteArrayBigEndian (blake_final_one.extract 0 4) = 0 := by
    rw [← blake_price blake_final_one (by decide +kernel), byte_list]
    decide +kernel
  generalize blake_final_one = d at core sz flag header ⊢
  refine ⟨core, ?_⟩
  exact congrArg Prod.fst (blake_valid_one default (UInt256.ofNat 1) default (input d)
    (by change fromByteArrayBigEndian (d.extract 0 4) ≤ 1; rw [header]; decide) sz flag)

theorem bls_discount_boundaries :
    [0,1,128,129].map (fun n => Bls12381.g1MsmGas (zeros (160*n))) = [0,12000,797184,803412] ∧
    [0,1,128,129].map (fun n => Bls12381.g2MsmGas (zeros (288*n))) = [0,22500,1509120,1520910] := by
  constructor
  all_goals simp only [List.map_cons, List.map_nil, Bls12381.g1MsmGas, Bls12381.g2MsmGas,
    zeros, List.length_replicate]
  all_goals decide +kernel

theorem blake_high_header : Osaka.gas .blake2f (array [1,0,0,0]).toList = 16777216 ∧
    fromByteArrayBigEndian ((array [1,0,0,0]).extract 0 4) = 16777216 := by
  constructor
  · rw [byte_list]; decide +kernel
  · simp only [fromByteArrayBigEndian, byte_list]; decide +kernel

def wide_base : ByteArray := array (word 33 ++ word 1 ++ word 1 ++ [1] ++ zeros 31 ++ [1,1,3])

/-- Exact input-representation counterexample at the conversion used by
Ξ_EXPMOD. This is not an output-equivalence or native-runtime theorem. -/
theorem modexp_base_truncation : Modexp.modexp wide_base.toList = some [2] ∧
    nat_of_slice wide_base 96 33 = 2^256+1 ∧
    (UInt256.ofNat (nat_of_slice wide_base 96 33)).toNat = 1 := by
  have base : nat_of_slice wide_base 96 33 = 2^256+1 := by
    simp only [nat_of_slice, fromByteArrayBigEndian, byte_list]
    decide +kernel
  refine ⟨?_, base, ?_⟩
  · rw [byte_list]; decide +kernel
  · rw [base]; decide +kernel

end SolidityBridge.PrecompileAgreement.Controls
