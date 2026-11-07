import SolidityBridge.PrecompileAgreement.Controls
import Lean

/-! Whole frozen types only; not a joint-premise witness or compiler-success theorem. Private terms below resolve one actual imported kernel constant and pass ordinary example type checking. No axiom or interface declaration is substituted. -/
open Solidity Solidity.Precompiles Solidity.Roadmap.Evm EvmYul

open Lean Elab Term in
elab "audit_private%" id:ident : term => do
  let env ← getEnv
  let suffix := "." ++ id.getId.toString
  let found := env.constants.toList.filter fun (n, _) =>
    n.toString.startsWith "_private.SolidityBridge.PrecompileAgreement." && n.toString.endsWith suffix
  unless found.length = 1 do throwError "expected one actual frozen private constant: {id}"
  let (name, info) := found.head!
  unless info.levelParams.isEmpty do throwError "unexpected universe parameters: {name}"
  logInfo m!"PRIVATE_CONSTANT {id.getId}: {name}"
  return mkConst name

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.list_loop
set_option linter.unusedVariables false in
example : ∀ (b : ByteArray) (i : Nat) (r : List UInt8), ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := audit_private% SolidityBridge.PrecompileAgreement.list_loop
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.byte_list
set_option linter.unusedVariables false in
example : ∀ (b : ByteArray), b.toList = b.data.toList := @SolidityBridge.PrecompileAgreement.byte_list
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.byte_length
set_option linter.unusedVariables false in
example : ∀ (b : ByteArray), b.toList.length = b.size := @SolidityBridge.PrecompileAgreement.byte_length
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.ofNat_nat
set_option linter.unusedVariables false in
example : ∀ (n : Nat) (h : n < UInt256.size), (UInt256.ofNat n).toNat = n := @SolidityBridge.PrecompileAgreement.ofNat_nat
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.subtract_nat
set_option linter.unusedVariables false in
example : ∀ (g : UInt256) (n : Nat) (h : n ≤ g.toNat), (g - UInt256.ofNat n).toNat = g.toNat - n := @SolidityBridge.PrecompileAgreement.subtract_nat
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.words_multiple
set_option linter.unusedVariables false in
example : ∀ (n : Nat), words (32 * n) = n := @SolidityBridge.PrecompileAgreement.words_multiple
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.words_next
set_option linter.unusedVariables false in
example : ∀ (n : Nat), words (32 * n + 1) = n + 1 := @SolidityBridge.PrecompileAgreement.words_next
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.words_last
set_option linter.unusedVariables false in
example : ∀ (n : Nat), words (32 * n + 31) = n + 1 := @SolidityBridge.PrecompileAgreement.words_last
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.words_boundary
set_option linter.unusedVariables false in
example : ∀ (n : Nat), words (32 * n + 32) = n + 1 := @SolidityBridge.PrecompileAgreement.words_boundary
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.words_rounding
set_option linter.unusedVariables false in
example : ∀ (n : Nat), words n = n / 32 + if n % 32 = 0 then 0 else 1 := @SolidityBridge.PrecompileAgreement.words_rounding
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.identity_lengths
set_option linter.unusedVariables false in
example : lengths.map (fun n => identityGas (filled n).toList) =
    [15,18,18,18,21,21,21,24] := @SolidityBridge.PrecompileAgreement.Controls.identity_lengths
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.sha_lengths
set_option linter.unusedVariables false in
example : lengths.map (fun n => Osaka.gas .sha256 (filled n).toList) =
    [60,72,72,72,84,84,84,96] := @SolidityBridge.PrecompileAgreement.Controls.sha_lengths
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.ripemd_lengths
set_option linter.unusedVariables false in
example : lengths.map (fun n => Osaka.gas .ripemd160 (filled n).toList) =
    [600,720,720,720,840,840,840,960] := @SolidityBridge.PrecompileAgreement.Controls.ripemd_lengths
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.identity_nonzero_output
set_option linter.unusedVariables false in
example : (Ξ_ID default (UInt256.ofNat 18) default (input (array [0,128,255,1]))).2.2.2.2 =
      array [0,128,255,1] := @SolidityBridge.PrecompileAgreement.Controls.identity_nonzero_output
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.identity_boundary
set_option linter.unusedVariables false in
example : (Ξ_ID default (UInt256.ofNat 17) default (input (array [0,128,255,1]))).1 = false ∧
    (Ξ_ID default (UInt256.ofNat 18) default (input (array [0,128,255,1]))).1 = true ∧
    (Ξ_ID default (UInt256.ofNat 19) default (input (array [0,128,255,1]))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.identity_boundary
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.sha_boundary
set_option linter.unusedVariables false in
example : (Ξ_SHA256 default (UInt256.ofNat 71) default (input (array [97,98,99]))).1 = false ∧
    (Ξ_SHA256 default (UInt256.ofNat 72) default (input (array [97,98,99]))).1 = true ∧
    (Ξ_SHA256 default (UInt256.ofNat 73) default (input (array [97,98,99]))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.sha_boundary
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.ripemd_boundary
set_option linter.unusedVariables false in
example : (Ξ_RIP160 default (UInt256.ofNat 719) default (input (array [97,98,99]))).1 = false ∧
    (Ξ_RIP160 default (UInt256.ofNat 720) default (input (array [97,98,99]))).1 = true ∧
    (Ξ_RIP160 default (UInt256.ofNat 721) default (input (array [97,98,99]))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.ripemd_boundary
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.ecrecover_controls
set_option linter.unusedVariables false in
example : ecrecover invalid_recovery = some [] ∧
    (Ξ_ECREC default (UInt256.ofNat 2999) default (input (array invalid_recovery))).1 = false ∧
    (Ξ_ECREC default (UInt256.ofNat 3000) default (input (array invalid_recovery))).1 = true ∧
    (Ξ_ECREC default (UInt256.ofNat 3001) default (input (array invalid_recovery))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.ecrecover_controls
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.bnadd_controls
set_option linter.unusedVariables false in
example : ([127,128,129].map (fun n => (Bn254.add (zeros n)).isSome)) = [true,true,true] ∧
    (Bn254.add bad_point).isNone = true ∧
    (Ξ_BN_ADD default (UInt256.ofNat 149) default (input (array (zeros 128)))).1 = false ∧
    (Ξ_BN_ADD default (UInt256.ofNat 150) default (input (array (zeros 128)))).1 = true ∧
    (Ξ_BN_ADD default (UInt256.ofNat 151) default (input (array (zeros 128)))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.bnadd_controls
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.bnmul_controls
set_option linter.unusedVariables false in
example : ([95,96,97].map (fun n => (Bn254.mul (zeros n)).isSome)) = [true,true,true] ∧
    (Bn254.mul (bad_point.take 96)).isNone = true ∧
    (Ξ_BN_MUL default (UInt256.ofNat 5999) default (input (array (zeros 96)))).1 = false ∧
    (Ξ_BN_MUL default (UInt256.ofNat 6000) default (input (array (zeros 96)))).1 = true ∧
    (Ξ_BN_MUL default (UInt256.ofNat 6001) default (input (array (zeros 96)))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.bnmul_controls
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.pairing_controls
set_option linter.unusedVariables false in
example : ([0,1,191,192,193,383,384,385].map (fun n => (Bn254.pairing (zeros n)).isNone)) =
      [false,true,true,false,true,true,false,true] ∧
    (Ξ_SNARKV default (UInt256.ofNat 78999) default (input (array (zeros 192)))).1 = false ∧
    (Ξ_SNARKV default (UInt256.ofNat 79000) default (input (array (zeros 192)))).1 = true ∧
    (Ξ_SNARKV default (UInt256.ofNat 79001) default (input (array (zeros 192)))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.pairing_controls
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_controls
set_option linter.unusedVariables false in
example : Osaka.gas .blake2f blake_one.toList = 1 ∧
    (Blake2f.blake2f blake_one.toList).isSome = true ∧
    (Blake2f.blake2f blake_bad_flag.toList).isNone = true ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 0) default (input blake_one)).1 = false ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 1) default (input blake_one)).1 = true ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 2) default (input blake_one)).2.2.1.toNat = 1 ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 2) default (input blake_bad_flag)).1 = false ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 2) default (input blake_bad_flag)).2.2.1.toNat = 0 := @SolidityBridge.PrecompileAgreement.Controls.blake_controls
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_short_mismatch
set_option linter.unusedVariables false in
example : Osaka.gas .blake2f (array [1]).toList = 16777216 ∧
    fromByteArrayBigEndian ((array [1]).extract 0 4) = 1 ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 1) default (input (array [1]))).1 = false := @SolidityBridge.PrecompileAgreement.Controls.blake_short_mismatch
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_byte_order
set_option linter.unusedVariables false in
example : Osaka.gas .blake2f (array [1,2,3,4]).toList = 16909060 ∧
    fromByteArrayBigEndian ((array [1,2,3,4]).extract 0 4) = 16909060 := @SolidityBridge.PrecompileAgreement.Controls.blake_byte_order
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.point_controls
set_option linter.unusedVariables false in
example : ([0,191,192,193].map (fun n => (PointEval.pointEval (zeros n)).isNone)) =
    [true,true,true,true] ∧
    (Ξ_PointEval default (UInt256.ofNat 49999) default (input (array (zeros 192)))).1 = false ∧
    (Ξ_PointEval default (UInt256.ofNat 50000) default (input (array (zeros 192)))).1 = true ∧
    (Ξ_PointEval default (UInt256.ofNat 50001) default (input (array (zeros 192)))).2.2.1.toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.point_controls
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.ffi_logical_mismatch
set_option linter.unusedVariables false in
example : (Bn254.add bad_point).isNone = true ∧
    (Ξ_BN_ADD default (UInt256.ofNat 150) default (input (array bad_point))).1 = true ∧
    (PointEval.pointEval (zeros 192)).isNone = true ∧
    (Ξ_PointEval default (UInt256.ofNat 50000) default (input (array (zeros 192)))).1 = true := @SolidityBridge.PrecompileAgreement.Controls.ffi_logical_mismatch
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.modexp_empty_mismatch
set_option linter.unusedVariables false in
example : Modexp.gas [] = 500 ∧
    (Ξ_EXPMOD default (UInt256.ofNat 200) default (input (array []))).1 = true ∧
    (Ξ_EXPMOD default (UInt256.ofNat 200) default (input (array []))).2.2.1.toNat = 0 := @SolidityBridge.PrecompileAgreement.Controls.modexp_empty_mismatch
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.modexp_bound_mismatch
set_option linter.unusedVariables false in
example : (Modexp.modexp oversized_modexp).isNone = true ∧
    Modexp.gas oversized_modexp = 0 ∧
    (Ξ_EXPMOD default (UInt256.ofNat 6000) default (input (array oversized_modexp))).1 = true ∧
    (Ξ_EXPMOD default (UInt256.ofNat 6000) default (input (array oversized_modexp))).2.2.1.toNat = 453 := @SolidityBridge.PrecompileAgreement.Controls.modexp_bound_mismatch
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.unsupported_core
set_option linter.unusedVariables false in
example : unsupported.map (fun p => (Osaka.run p []).isNone) =
    [true,true,true,true,true,true,true,false] ∧
    unsupported.map (fun p => Osaka.gas p []) = [375,0,600,0,37700,5500,23800,6900] := @SolidityBridge.PrecompileAgreement.Controls.unsupported_core
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (n : Nat) (member : n ∈ [0,1,2,3,4,212,214]), Ξ_BLAKE2_F σ g A (input (filled n)) = (false, ∅, ⟨0⟩, A, .empty) := @SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_core_lengths
set_option linter.unusedVariables false in
example : [0,1,2,3,4,212,213,214].map (fun n => (Blake2f.blake2f (zeros n)).isSome) =
      [false,false,false,false,false,false,true,false] := @SolidityBridge.PrecompileAgreement.Controls.blake_core_lengths
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_final_one_control
set_option linter.unusedVariables false in
example : (Blake2f.blake2f blake_final_one.toList).isSome = true ∧
    (Ξ_BLAKE2_F default (UInt256.ofNat 1) default (input blake_final_one)).1 = true := @SolidityBridge.PrecompileAgreement.Controls.blake_final_one_control
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.bls_discount_boundaries
set_option linter.unusedVariables false in
example : [0,1,128,129].map (fun n => Bls12381.g1MsmGas (zeros (160*n))) = [0,12000,797184,803412] ∧
    [0,1,128,129].map (fun n => Bls12381.g2MsmGas (zeros (288*n))) = [0,22500,1509120,1520910] := @SolidityBridge.PrecompileAgreement.Controls.bls_discount_boundaries
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_high_header
set_option linter.unusedVariables false in
example : Osaka.gas .blake2f (array [1,0,0,0]).toList = 16777216 ∧
    fromByteArrayBigEndian ((array [1,0,0,0]).extract 0 4) = 16777216 := @SolidityBridge.PrecompileAgreement.Controls.blake_high_header
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement.Controls
-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.modexp_base_truncation
set_option linter.unusedVariables false in
example : Modexp.modexp wide_base.toList = some [2] ∧
    nat_of_slice wide_base 96 33 = 2^256+1 ∧
    (UInt256.ofNat (nat_of_slice wide_base 96 33)).toNat = 1 := @SolidityBridge.PrecompileAgreement.Controls.modexp_base_truncation
end SolidityBridge.PrecompileAgreement.Controls

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.address_table
set_option linter.unusedVariables false in
example : Precompile.all.map Precompile.address =
    [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,256] := @SolidityBridge.PrecompileAgreement.address_table
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.address_complete
set_option linter.unusedVariables false in
example : ∀ (p : Precompile), p ∈ Precompile.all := @SolidityBridge.PrecompileAgreement.address_complete
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.sha_price
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), Osaka.gas .sha256 d.toList = 60 + 12 * ((d.size + 31) / 32) := @SolidityBridge.PrecompileAgreement.sha_price
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.ripemd_price
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), Osaka.gas .ripemd160 d.toList = 600 + 120 * ((d.size + 31) / 32) := @SolidityBridge.PrecompileAgreement.ripemd_price
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.pairing_price
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), Osaka.gas .bnPairing d.toList = 34000 * (d.size / 192) + 45000 := @SolidityBridge.PrecompileAgreement.pairing_price
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.ecrecover_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_ECREC σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .ecrecover I.calldata.toList then 0
      else g.toNat - Osaka.gas .ecrecover I.calldata.toList := @SolidityBridge.PrecompileAgreement.ecrecover_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.sha_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_SHA256 σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .sha256 I.calldata.toList then 0
      else g.toNat - Osaka.gas .sha256 I.calldata.toList := @SolidityBridge.PrecompileAgreement.sha_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.ripemd_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_RIP160 σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .ripemd160 I.calldata.toList then 0
      else g.toNat - Osaka.gas .ripemd160 I.calldata.toList := @SolidityBridge.PrecompileAgreement.ripemd_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.bnadd_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_BN_ADD σ g A I).2.2.1.toNat =
      if (Ξ_BN_ADD σ g A I).1 then g.toNat - Osaka.gas .bnAdd I.calldata.toList else 0 := @SolidityBridge.PrecompileAgreement.bnadd_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.bnmul_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_BN_MUL σ g A I).2.2.1.toNat =
      if (Ξ_BN_MUL σ g A I).1 then g.toNat - Osaka.gas .bnMul I.calldata.toList else 0 := @SolidityBridge.PrecompileAgreement.bnmul_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.pairing_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_SNARKV σ g A I).2.2.1.toNat =
      if (Ξ_SNARKV σ g A I).1 then g.toNat - Osaka.gas .bnPairing I.calldata.toList else 0 := @SolidityBridge.PrecompileAgreement.pairing_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.point_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_PointEval σ g A I).2.2.1.toNat =
      if (Ξ_PointEval σ g A I).1 then g.toNat - Osaka.gas .pointEvaluation I.calldata.toList else 0 := @SolidityBridge.PrecompileAgreement.point_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.be_append_byte
set_option linter.unusedVariables false in
example : ∀ (bs : List UInt8) (b : UInt8), ofBE ((bs ++ [b]).map UInt8.toNat) = 256 * ofBE (bs.map UInt8.toNat) + b.toNat := audit_private% SolidityBridge.PrecompileAgreement.be_append_byte
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.little_reader
set_option linter.unusedVariables false in
example : ∀ (bs : List UInt8), fromBytes' bs = ofBE (bs.reverse.map UInt8.toNat) := audit_private% SolidityBridge.PrecompileAgreement.little_reader
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.big_reader
set_option linter.unusedVariables false in
example : ∀ (bs : List UInt8), fromBytesBigEndian bs = ofBE (bs.map UInt8.toNat) := @SolidityBridge.PrecompileAgreement.big_reader
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.first_four
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), (d.extract 0 4).toList = d.toList.take 4 := @SolidityBridge.PrecompileAgreement.first_four
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.append_zero
set_option linter.unusedVariables false in
example : ∀ (bs : List Nat), ofBE (bs ++ [0]) = 256 * ofBE bs := audit_private% SolidityBridge.PrecompileAgreement.append_zero
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.zero_padding
set_option linter.unusedVariables false in
example : ∀ (bs : List Nat) (n : Nat), ofBE (bs ++ List.replicate n 0) = ofBE bs * 256 ^ n := @SolidityBridge.PrecompileAgreement.zero_padding
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_padding
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), Osaka.gas .blake2f d.toList =
      fromByteArrayBigEndian (d.extract 0 4) * 256 ^ (4 - min 4 d.size) := @SolidityBridge.PrecompileAgreement.blake_padding
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_zero_header
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray)
    (zero : fromByteArrayBigEndian (d.extract 0 4) = 0), Osaka.gas .blake2f d.toList = 0 := @SolidityBridge.PrecompileAgreement.blake_zero_header
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_price
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray) (header : 4 ≤ d.size), Osaka.gas .blake2f d.toList = fromByteArrayBigEndian (d.extract 0 4) := @SolidityBridge.PrecompileAgreement.blake_price
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (header : 4 ≤ I.calldata.size), (Ξ_BLAKE2_F σ g A I).2.2.1.toNat =
      if (Ξ_BLAKE2_F σ g A I).1 then g.toNat - Osaka.gas .blake2f I.calldata.toList else 0 := @SolidityBridge.PrecompileAgreement.blake_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_valid
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : fromByteArrayBigEndian (I.calldata.extract 0 4) ≤ g.toNat)
    (size : I.calldata.size = 213) (flag : I.calldata[212]! = 0), Ξ_BLAKE2_F σ g A I =
      (true, σ, g - .ofNat (fromByteArrayBigEndian (I.calldata.extract 0 4)), A,
        ffi.BLAKE2Compress I.calldata) := @SolidityBridge.PrecompileAgreement.blake_valid
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_insufficient
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (short : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)), Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty) := @SolidityBridge.PrecompileAgreement.blake_insufficient
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_invalid_flag
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (size : I.calldata.size = 213) (flag : I.calldata[212]! = 2), Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty) := @SolidityBridge.PrecompileAgreement.blake_invalid_flag
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_valid_one
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : fromByteArrayBigEndian (I.calldata.extract 0 4) ≤ g.toNat)
    (size : I.calldata.size = 213) (flag : I.calldata[212]! = 1), Ξ_BLAKE2_F σ g A I =
      (true, σ, g - .ofNat (fromByteArrayBigEndian (I.calldata.extract 0 4)), A,
        ffi.BLAKE2Compress I.calldata) := @SolidityBridge.PrecompileAgreement.blake_valid_one
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_invalid_size
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (size : I.calldata.size ≠ 213), Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty) := @SolidityBridge.PrecompileAgreement.blake_invalid_size
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.blake_zero_gas
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (zero : fromByteArrayBigEndian (I.calldata.extract 0 4) = 0), (Ξ_BLAKE2_F σ g A I).2.2.1.toNat =
      if (Ξ_BLAKE2_F σ g A I).1 then g.toNat - Osaka.gas .blake2f I.calldata.toList else 0 := @SolidityBridge.PrecompileAgreement.blake_zero_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_gas
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), identityGas d.toList = 15 + 3 * ((d.size + 31) / 32) := @SolidityBridge.PrecompileAgreement.identity_gas
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_output
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), identity d.toList = some d.toList := @SolidityBridge.PrecompileAgreement.identity_output
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_run
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), Ξ_ID σ g A I =
      if g.toNat < identityGas I.calldata.toList then (false, ∅, ⟨0⟩, A, ByteArray.empty)
      else (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata) := @SolidityBridge.PrecompileAgreement.identity_run
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_success
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : identityGas I.calldata.toList ≤ g.toNat), Ξ_ID σ g A I = (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata) := @SolidityBridge.PrecompileAgreement.identity_success
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_failure
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (short : g.toNat < identityGas I.calldata.toList), Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty) := @SolidityBridge.PrecompileAgreement.identity_failure
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_charged
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : identityGas I.calldata.toList ≤ g.toNat), (Ξ_ID σ g A I).2.2.1.toNat + identityGas I.calldata.toList = g.toNat := @SolidityBridge.PrecompileAgreement.identity_charged
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_success_iff
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_ID σ g A I).1 = true ↔ identityGas I.calldata.toList ≤ g.toNat := @SolidityBridge.PrecompileAgreement.identity_success_iff
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_exact
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (fits : identityGas I.calldata.toList < UInt256.size), Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList)) A I =
      (true, σ, UInt256.ofNat 0, A, I.calldata) := @SolidityBridge.PrecompileAgreement.identity_exact
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_one_short
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (fits : identityGas I.calldata.toList < UInt256.size), Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList - 1)) A I =
      (false, ∅, ⟨0⟩, A, ByteArray.empty) := @SolidityBridge.PrecompileAgreement.identity_one_short
end SolidityBridge.PrecompileAgreement

namespace SolidityBridge.PrecompileAgreement
-- Frozen source: SolidityBridge.PrecompileAgreement.identity_unaffordable
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (huge : UInt256.size ≤ identityGas I.calldata.toList), Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty) := @SolidityBridge.PrecompileAgreement.identity_unaffordable
end SolidityBridge.PrecompileAgreement

run_cmd Lean.logInfo "BRIDGE_FULL_TYPE_FIDELITY_PASS total=73 private=4 closed=25"
