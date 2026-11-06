import Solidity.Precompiles.Field
import Solidity.Precompiles.Basic
import Solidity.Precompiles.Modexp
import Solidity.Precompiles.Bn254
import Solidity.Precompiles.Blake2f
import Solidity.Precompiles.P256

/-! Concrete domains for the 17 remaining buildable unconditional declarations.
These statements have data binders and no proof hypotheses. Their existential
samples instantiate the exact conclusion; they are counted separately from the
seven existing simultaneous proof-premise witnesses. No compiler-success result
or cryptographic agreement follows from this applicability census. -/
namespace H62.AuditPrecompiles
open Solidity.Precompiles Solidity.Roadmap.Evm

theorem readPad_length_data : ∃ (d : Bytes) (start len : Nat),
    (readPad d start len).length = len :=
  ⟨[1], 0, 2, readPad_length [1] 0 2⟩

theorem toBE_length_data : ∃ k n : Nat, (toBE k n).length = k :=
  ⟨2, 257, toBE_length 2 257⟩

theorem mapM_eq_none_iff_data : ∃ (f : Unit → Option Unit) (l : List Unit),
    l.mapM f = none ↔ ∃ a ∈ l, f a = none :=
  ⟨some, [()], mapM_eq_none_iff some [()]⟩

theorem ecrecover_isSome_data : ∃ d : Bytes, (ecrecover d).isSome :=
  ⟨[1], ecrecover_isSome [1]⟩

theorem sha256_isSome_data : ∃ d : Bytes, (sha256 d).isSome :=
  ⟨[1], sha256_isSome [1]⟩

theorem ripemd160_isSome_data : ∃ d : Bytes, (ripemd160 d).isSome :=
  ⟨[1], ripemd160_isSome [1]⟩

theorem identity_eq_data : ∃ d : Bytes, identity d = some d :=
  ⟨[1], identity_eq [1]⟩

theorem modexp_eq_none_iff_data : ∃ d : Bytes,
    Modexp.modexp d = none ↔ Modexp.Malformed d :=
  ⟨[], Modexp.modexp_eq_none_iff []⟩

theorem bn_add_eq_none_iff_data : ∃ d : Bytes,
    Bn254.add d = none ↔ Bn254.decodeG1 (readPad d 0 64) = none ∨
      Bn254.decodeG1 (readPad d 64 64) = none :=
  ⟨[], Bn254.add_eq_none_iff []⟩

theorem bn_mul_eq_none_iff_data : ∃ d : Bytes,
    Bn254.mul d = none ↔ Bn254.decodeG1 (readPad d 0 64) = none :=
  ⟨[], Bn254.mul_eq_none_iff []⟩

theorem bn_onCurve_aff_data : ∃ x y : Bn254.Fp,
    Bn254.curve.onCurve (.aff x y) =
      decide (y.val * y.val % Bn254.p = (x.val * x.val * x.val + 3) % Bn254.p) :=
  ⟨1, 2, Bn254.onCurve_aff 1 2⟩

theorem bn_decodeG1_eq_none_iff_data : ∃ b : List Nat,
    Bn254.decodeG1 b = none ↔
      let x := ofBE (b.take 32)
      let y := ofBE ((b.drop 32).take 32)
      Bn254.p ≤ x ∨ Bn254.p ≤ y ∨
        ¬(x = 0 ∧ y = 0) ∧ y * y % Bn254.p ≠ (x * x * x + 3) % Bn254.p :=
  ⟨[], Bn254.decodeG1_eq_none_iff []⟩

theorem bn_pairing_eq_none_iff_data : ∃ d : Bytes,
    Bn254.pairing d = none ↔ d.length % 192 ≠ 0 ∨
      ∃ b ∈ chunks 192 (d.map UInt8.toNat), Bn254.decodePair b = none :=
  ⟨[], Bn254.pairing_eq_none_iff []⟩

theorem blake_compress_size_data : ∃ (rounds : Nat) (h m : Array UInt64)
    (t₀ t₁ : UInt64) (f : Bool), (Blake2f.compress rounds h m t₀ t₁ f).size = 8 :=
  ⟨0, Array.replicate 8 0, Array.replicate 16 0, 0, 0, false,
    Blake2f.compress_size 0 (Array.replicate 8 0) (Array.replicate 16 0) 0 0 false⟩

theorem blake_flatMap_length_data : ∃ l : List UInt64,
    (l.flatMap fun w => (toBE 8 w.toNat).reverse).length = 8 * l.length :=
  ⟨[1], Blake2f.flatMap_length [1]⟩

theorem blake_eq_none_iff_data : ∃ d : Bytes,
    Blake2f.blake2f d = none ↔ d.length ≠ 213 ∨ 1 < Blake2f.flag d :=
  ⟨[], Blake2f.blake2f_eq_none_iff []⟩

theorem p256_isSome_data : ∃ d : Bytes, (P256.p256Verify d).isSome :=
  ⟨[1], P256.p256Verify_isSome [1]⟩

#print axioms readPad_length_data
#print axioms toBE_length_data
#print axioms mapM_eq_none_iff_data
#print axioms ecrecover_isSome_data
#print axioms sha256_isSome_data
#print axioms ripemd160_isSome_data
#print axioms identity_eq_data
#print axioms modexp_eq_none_iff_data
#print axioms bn_add_eq_none_iff_data
#print axioms bn_mul_eq_none_iff_data
#print axioms bn_onCurve_aff_data
#print axioms bn_decodeG1_eq_none_iff_data
#print axioms bn_pairing_eq_none_iff_data
#print axioms blake_compress_size_data
#print axioms blake_flatMap_length_data
#print axioms blake_eq_none_iff_data
#print axioms p256_isSome_data
end H62.AuditPrecompiles
