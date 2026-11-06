import Solidity.Precompiles.Field
import Solidity.Precompiles.Basic
import Solidity.Precompiles.Modexp
import Solidity.Precompiles.Bn254
import Solidity.Precompiles.Blake2f
import Solidity.Precompiles.P256

/-! Every example assigns the original constant directly at its entire frozen
source type, including all data and proof binders. This does not replace
a simultaneous applicability witness or owner compiler-success theorem.
Unused binder lint is local to these type checks: every frozen proof binder
is retained with its original name even when absent from the conclusion. -/
open Solidity.Roadmap.Evm (Bytes)

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.readPad_length
set_option linter.unusedVariables false in
example : ∀ (d : Bytes) (start len : Nat), (readPad d start len).length = len := @Solidity.Precompiles.readPad_length
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.toBE_length
set_option linter.unusedVariables false in
example : ∀ (k n : Nat), (toBE k n).length = k := @Solidity.Precompiles.toBE_length
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.mapM_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ {α β : Type} (f : α → Option β) (l : List α), l.mapM f = none ↔ ∃ a ∈ l, f a = none := @Solidity.Precompiles.mapM_eq_none_iff
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.ecrecover_isSome
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), (ecrecover d).isSome := @Solidity.Precompiles.ecrecover_isSome
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.sha256_isSome
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), (sha256 d).isSome := @Solidity.Precompiles.sha256_isSome
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.ripemd160_isSome
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), (ripemd160 d).isSome := @Solidity.Precompiles.ripemd160_isSome
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.identity_eq
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), identity d = some d := @Solidity.Precompiles.identity_eq
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.words_mono
set_option linter.unusedVariables false in
example : ∀ {m n : Nat} (h : m ≤ n), words m ≤ words n := @Solidity.Precompiles.words_mono
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.sha256Gas_mono
set_option linter.unusedVariables false in
example : ∀ {d e : Bytes} (h : d.length ≤ e.length), sha256Gas d ≤ sha256Gas e := @Solidity.Precompiles.sha256Gas_mono
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.ripemd160Gas_mono
set_option linter.unusedVariables false in
example : ∀ {d e : Bytes} (h : d.length ≤ e.length), ripemd160Gas d ≤ ripemd160Gas e := @Solidity.Precompiles.ripemd160Gas_mono
end Solidity.Precompiles

namespace Solidity.Precompiles
-- Frozen source: Solidity.Precompiles.identityGas_mono
set_option linter.unusedVariables false in
example : ∀ {d e : Bytes} (h : d.length ≤ e.length), identityGas d ≤ identityGas e := @Solidity.Precompiles.identityGas_mono
end Solidity.Precompiles

namespace Solidity.Precompiles.Modexp
-- Frozen source: Solidity.Precompiles.Modexp.modexp_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), modexp d = none ↔ Malformed d := @Solidity.Precompiles.Modexp.modexp_eq_none_iff
end Solidity.Precompiles.Modexp

namespace Solidity.Precompiles.Modexp
-- Frozen source: Solidity.Precompiles.Modexp.modexp_length
set_option linter.unusedVariables false in
example : ∀ {d o : Bytes} (h : modexp d = some o), o.length = modLen d := @Solidity.Precompiles.Modexp.modexp_length
end Solidity.Precompiles.Modexp

namespace Solidity.Precompiles.Modexp
-- Frozen source: Solidity.Precompiles.Modexp.gas_ge
set_option linter.unusedVariables false in
example : ∀ {d : Bytes} (h : ¬Malformed d), 500 ≤ gas d := @Solidity.Precompiles.Modexp.gas_ge
end Solidity.Precompiles.Modexp

namespace Solidity.Precompiles.Bn254
-- Frozen source: Solidity.Precompiles.Bn254.add_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), add d = none ↔ decodeG1 (readPad d 0 64) = none ∨ decodeG1 (readPad d 64 64) = none := @Solidity.Precompiles.Bn254.add_eq_none_iff
end Solidity.Precompiles.Bn254

namespace Solidity.Precompiles.Bn254
-- Frozen source: Solidity.Precompiles.Bn254.mul_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), mul d = none ↔ decodeG1 (readPad d 0 64) = none := @Solidity.Precompiles.Bn254.mul_eq_none_iff
end Solidity.Precompiles.Bn254

namespace Solidity.Precompiles.Bn254
-- Frozen source: Solidity.Precompiles.Bn254.onCurve_aff
set_option linter.unusedVariables false in
example : ∀ (x y : Fp), curve.onCurve (.aff x y) = decide (y.val * y.val % p = (x.val * x.val * x.val + 3) % p) := @Solidity.Precompiles.Bn254.onCurve_aff
end Solidity.Precompiles.Bn254

namespace Solidity.Precompiles.Bn254
-- Frozen source: Solidity.Precompiles.Bn254.decodeG1_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (b : List Nat), decodeG1 b = none ↔
      let x := ofBE (b.take 32)
      let y := ofBE ((b.drop 32).take 32)
      p ≤ x ∨ p ≤ y ∨ ¬(x = 0 ∧ y = 0) ∧ y * y % p ≠ (x * x * x + 3) % p := @Solidity.Precompiles.Bn254.decodeG1_eq_none_iff
end Solidity.Precompiles.Bn254

namespace Solidity.Precompiles.Bn254
-- Frozen source: Solidity.Precompiles.Bn254.pairing_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), pairing d = none ↔ d.length % 192 ≠ 0 ∨
      ∃ b ∈ chunks 192 (d.map UInt8.toNat), decodePair b = none := @Solidity.Precompiles.Bn254.pairing_eq_none_iff
end Solidity.Precompiles.Bn254

namespace Solidity.Precompiles.Blake2f
-- Frozen source: Solidity.Precompiles.Blake2f.compress_size
set_option linter.unusedVariables false in
example : ∀ (rounds : Nat) (h m : Array UInt64) (t₀ t₁ : UInt64) (f : Bool), (compress rounds h m t₀ t₁ f).size = 8 := @Solidity.Precompiles.Blake2f.compress_size
end Solidity.Precompiles.Blake2f

namespace Solidity.Precompiles.Blake2f
-- Frozen source: Solidity.Precompiles.Blake2f.flatMap_length
set_option linter.unusedVariables false in
example : ∀ (l : List UInt64), (l.flatMap fun w => (toBE 8 w.toNat).reverse).length = 8 * l.length := @Solidity.Precompiles.Blake2f.flatMap_length
end Solidity.Precompiles.Blake2f

namespace Solidity.Precompiles.Blake2f
-- Frozen source: Solidity.Precompiles.Blake2f.blake2f_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), blake2f d = none ↔ d.length ≠ 213 ∨ 1 < flag d := @Solidity.Precompiles.Blake2f.blake2f_eq_none_iff
end Solidity.Precompiles.Blake2f

namespace Solidity.Precompiles.Blake2f
-- Frozen source: Solidity.Precompiles.Blake2f.blake2f_length
set_option linter.unusedVariables false in
example : ∀ {d o : Bytes} (h : blake2f d = some o), o.length = 64 := @Solidity.Precompiles.Blake2f.blake2f_length
end Solidity.Precompiles.Blake2f

namespace Solidity.Precompiles.P256
-- Frozen source: Solidity.Precompiles.P256.p256Verify_isSome
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), (p256Verify d).isSome := @Solidity.Precompiles.P256.p256Verify_isSome
end Solidity.Precompiles.P256
