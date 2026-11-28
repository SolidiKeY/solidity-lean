import Solidity.Precompiles.Basic
import Solidity.Precompiles.Modexp
import Solidity.Precompiles.Bn254
import Solidity.Precompiles.Blake2f
import Solidity.Precompiles.P256
import Solidity.Precompiles.PointEval

namespace Solidity.Precompiles.Osaka

open Solidity.Roadmap.Evm

def run : Precompile → Bytes → Option Bytes
  | .ecrecover => ecrecover
  | .sha256 => sha256
  | .ripemd160 => ripemd160
  | .identity => identity
  | .modexp => Modexp.modexp
  | .bnAdd => Bn254.add
  | .bnMul => Bn254.mul
  | .bnPairing => Bn254.pairing
  | .blake2f => Blake2f.blake2f
  | .pointEvaluation => PointEval.pointEval
  | .blsG1Add => Bls12381.g1Add
  | .blsG1Msm => Bls12381.g1Msm
  | .blsG2Add => Bls12381.g2Add
  | .blsG2Msm => Bls12381.g2Msm
  | .blsPairing => Bls12381.pairing
  | .blsMapFpToG1 => Bls12381.mapFpToG1
  | .blsMapFp2ToG2 => Bls12381.mapFp2ToG2
  | .p256Verify => P256.p256Verify

def gas : Precompile → Bytes → Nat
  | .ecrecover => ecrecoverGas
  | .sha256 => sha256Gas
  | .ripemd160 => ripemd160Gas
  | .identity => identityGas
  | .modexp => Modexp.gas
  | .bnAdd => Bn254.addGas
  | .bnMul => Bn254.mulGas
  | .bnPairing => Bn254.pairingGas
  | .blake2f => Blake2f.gas
  | .pointEvaluation => PointEval.gas
  | .blsG1Add => Bls12381.g1AddGas
  | .blsG1Msm => Bls12381.g1MsmGas
  | .blsG2Add => Bls12381.g2AddGas
  | .blsG2Msm => Bls12381.g2MsmGas
  | .blsPairing => Bls12381.pairingGas
  | .blsMapFpToG1 => Bls12381.mapFpToG1Gas
  | .blsMapFp2ToG2 => Bls12381.mapFp2ToG2Gas
  | .p256Verify => P256.gas

def fixed : Fixed where
  keccak := keccakWord
  keccak_lt _ := Nat.mod_lt _ (Nat.pow_pos (by decide))
  precompile := run
  precompileGas := gas

theorem fixed_precompileGas : fixed.precompileGas = gas := rfl

def Malformed : Precompile → Bytes → Prop
  | .ecrecover, _ | .sha256, _ | .ripemd160, _ | .identity, _ | .p256Verify, _ => False
  | .modexp, d => Modexp.Malformed d
  | .bnAdd, d =>
    Bn254.decodeG1 (readPad d 0 64) = none ∨ Bn254.decodeG1 (readPad d 64 64) = none
  | .bnMul, d => Bn254.decodeG1 (readPad d 0 64) = none
  | .bnPairing, d =>
    d.length % 192 ≠ 0 ∨ ∃ b ∈ chunks 192 (d.map UInt8.toNat), Bn254.decodePair b = none
  | .blake2f, d => d.length ≠ 213 ∨ 1 < Blake2f.flag d
  | .pointEvaluation, d =>
    PointEval.decode d = none ∨ ∃ i, PointEval.decode d = some i ∧ PointEval.verifies i = false
  | .blsG1Add, d =>
    d.length ≠ 256 ∨ Bls12381.decodeG1 ((d.map UInt8.toNat).take 128) = none ∨
      Bls12381.decodeG1 ((d.map UInt8.toNat).drop 128) = none
  | .blsG1Msm, d =>
    d.length = 0 ∨ d.length % 160 ≠ 0 ∨
      ∃ c ∈ chunks 160 (d.map UInt8.toNat), Bls12381.decodeG1Sub (c.take 128) = none
  | .blsG2Add, d =>
    d.length ≠ 512 ∨ Bls12381.decodeG2 ((d.map UInt8.toNat).take 256) = none ∨
      Bls12381.decodeG2 ((d.map UInt8.toNat).drop 256) = none
  | .blsG2Msm, d =>
    d.length = 0 ∨ d.length % 288 ≠ 0 ∨
      ∃ c ∈ chunks 288 (d.map UInt8.toNat), Bls12381.decodeG2Sub (c.take 256) = none
  | .blsPairing, d =>
    d.length = 0 ∨ d.length % 384 ≠ 0 ∨
      ∃ c ∈ chunks 384 (d.map UInt8.toNat),
        Bls12381.decodeG1Sub (c.take 128) = none ∨ Bls12381.decodeG2Sub (c.drop 128) = none
  | .blsMapFpToG1, d => d.length ≠ 64 ∨ Bls12381.p ≤ ofBE (d.map UInt8.toNat)
  | .blsMapFp2ToG2, d => d.length ≠ 128 ∨ Bls12381.decodeFp2 (d.map UInt8.toNat) = none

theorem run_eq_none_iff (p : Precompile) (d : Bytes) : run p d = none ↔ Malformed p d := by
  cases p
  · exact ⟨(fun h => nomatch h), False.elim⟩
  · exact ⟨(fun h => nomatch h), False.elim⟩
  · exact ⟨(fun h => nomatch h), False.elim⟩
  · exact ⟨(fun h => nomatch h), False.elim⟩
  · exact Modexp.modexp_eq_none_iff d
  · exact Bn254.add_eq_none_iff d
  · exact Bn254.mul_eq_none_iff d
  · exact Bn254.pairing_eq_none_iff d
  · exact Blake2f.blake2f_eq_none_iff d
  · exact PointEval.pointEval_eq_none_iff d
  · exact Bls12381.g1Add_eq_none_iff d
  · exact Bls12381.g1Msm_eq_none_iff d
  · exact Bls12381.g2Add_eq_none_iff d
  · exact Bls12381.g2Msm_eq_none_iff d
  · exact Bls12381.pairing_eq_none_iff d
  · exact Bls12381.mapFpToG1_eq_none_iff d
  · exact Bls12381.mapFp2ToG2_eq_none_iff d
  · exact ⟨(fun h => nomatch h), False.elim⟩

theorem fixed_precompile_eq_none_iff (p : Precompile) (d : Bytes) :
    fixed.precompile p d = none ↔ Malformed p d :=
  run_eq_none_iff p d

def LengthPriced (p : Precompile) : Prop := p ≠ .modexp ∧ p ≠ .blake2f

theorem gas_mono {p : Precompile} (hp : LengthPriced p) {d e : Bytes}
    (h : d.length ≤ e.length) : gas p d ≤ gas p e := by
  cases p
  · exact Nat.le_refl _
  · exact sha256Gas_mono h
  · exact ripemd160Gas_mono h
  · exact identityGas_mono h
  · exact absurd rfl hp.1
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left 34000 (Nat.div_le_div_right h)) 45000
  · exact absurd rfl hp.2
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Bls12381.g1MsmGas_mono h
  · exact Nat.le_refl _
  · exact Bls12381.g2MsmGas_mono h
  · exact Bls12381.pairingGas_mono h
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem ecrecover_exceeds_stipend (d : Bytes) : pinned.stipend < gas .ecrecover d := by
  show pinned.stipend < 3000
  exact @of_decide_eq_true _ (Nat.decLt _ _) rfl

def stipendFits (p : Precompile) : Bool := (run p []).isSome && gas p [] ≤ pinned.stipend

#guard Precompile.all.filter stipendFits ==
  [.sha256, .ripemd160, .identity, .modexp, .bnAdd]

end Solidity.Precompiles.Osaka

/-- info: 'Solidity.Precompiles.Osaka.run_eq_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Precompiles.Osaka.run_eq_none_iff
/-- info: 'Solidity.Precompiles.Osaka.gas_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Precompiles.Osaka.gas_mono
/-- info: 'Solidity.Precompiles.Osaka.ecrecover_exceeds_stipend' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Precompiles.Osaka.ecrecover_exceeds_stipend
