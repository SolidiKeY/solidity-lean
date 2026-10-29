import Solidity.Precompiles.Pairing

/-!
# BN254 (alt_bn128): `ECADD` (0x06), `ECMUL` (0x07) and the pairing check (0x08)

EIP-196 and EIP-197 with Istanbul's gas (EIP-1108), as Osaka's execution
specification (`alt_bn128.py`) runs them:

- **Encoding.**  A `G1` point is two 32-byte big-endian coordinates below
  `p`, `(0, 0)` being infinity; a `G2` point is four, each `Fp2` element
  written imaginary part first.  A coordinate at or above `p`, or a point
  off its curve, is malformed: the call halts exceptionally.
- **`ECADD`** reads 128 bytes (zero-padded, the rest ignored) and returns
  the sum's 64 bytes; 150 gas.
- **`ECMUL`** reads 96 bytes, the scalar a full 256-bit word; 6000 gas.
- **The pairing check** takes `k` pairs of 192 bytes (`G1` then `G2`),
  failing when the length is not a multiple of 192 or a point is malformed
  or outside the order-`r` subgroup; it returns the word `1` when the
  pairings multiply to one, else `0`; `45000 + 34000·k` gas.

`add_eq_none_iff`, `mul_eq_none_iff` and `pairing_eq_none_iff` state the failure cases exactly; the `#guard`s are
vectors computed by the execution specification (Osaka) itself.
-/

namespace Solidity.Precompiles.Bn254

open Solidity.Roadmap.Evm (Bytes)

/-- The base field's prime. -/
def p : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
/-- The group order. -/
def r : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

instance : NeZero p := ⟨by decide⟩

abbrev Fp := Fin p

/-- `ξ = 9 + u`, the twist's non-residue. -/
def ξ : Fp2 p := ⟨9, 1⟩

/-- `G1`: `y² = x³ + 3`. -/
def curve : Curve Fp := ⟨0, 3⟩

/-- The D-twist `y² = x³ + 3/ξ` over `Fp2`, carrying `G2`. -/
def twist : Curve (Fp2 p) := ⟨FieldOps.zero, FieldOps.ofNat 3 * FieldOps.inv ξ⟩

/-- The generator of `G2` (EIP-197). -/
def g2 : Pt (Fp2 p) :=
  .aff ⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
        11559732032986387107991004021392285783925812861821192530917403151452391805634⟩
       ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
        4082367875863433681332203403145435568316851327593401208105741076214120093531⟩

/-- BN254 for the pairing check: `w¹² = 18·w⁶ - 82`, `u = w⁶ - 9`, the
D-twist (`t_k = w^k`), the ate loop count `6·x + 2` and the Frobenius
constants `ξ^((p-1)/3)`, `ξ^((p-1)/2)`. -/
def pairingCurve : PairingCurve p where
  order := r
  g1 := curve
  g2 := twist
  k₆ := 18
  k₀ := p - 82
  ξ := 9
  t₁ := Fp12.monomial 1
  t₂ := Fp12.monomial 2
  t₃ := Fp12.monomial 3
  loop := 29793968203157093288
  frob := some (FieldOps.pow ξ ((p - 1) / 3), FieldOps.pow ξ ((p - 1) / 2))

/-! ## Encoding -/

/-- A decoded `G1` point: on the curve. -/
abbrev G1 := { P : Pt Fp // curve.onCurve P = true }

/-- A decoded `G2` point: on the twist and in the order-`r` subgroup. -/
abbrev G2 := { Q : Pt (Fp2 p) // twist.onCurve Q = true ∧ twist.mul r Q = .inf }

/-- A coordinate: a number below `p`. -/
def coord (n : Nat) : Option Fp := if h : n < p then some ⟨n, h⟩ else none

/-- The `G1` point in 64 bytes, if well formed. -/
def decodeG1 (b : List Nat) : Option G1 := do
  let x ← coord (ofBE (b.take 32))
  let y ← coord (ofBE ((b.drop 32).take 32))
  let P : Pt Fp := if x.val = 0 ∧ y.val = 0 then .inf else .aff x y
  if h : curve.onCurve P = true then some ⟨P, h⟩ else none

/-- The `G2` point in 128 bytes (`x.im, x.re, y.im, y.re`), if well formed. -/
def decodeG2 (b : List Nat) : Option G2 := do
  let xi ← coord (ofBE (b.take 32))
  let xr ← coord (ofBE ((b.drop 32).take 32))
  let yi ← coord (ofBE ((b.drop 64).take 32))
  let yr ← coord (ofBE ((b.drop 96).take 32))
  let Q : Pt (Fp2 p) :=
    if xi.val = 0 ∧ xr.val = 0 ∧ yi.val = 0 ∧ yr.val = 0 then .inf else .aff ⟨xr, xi⟩ ⟨yr, yi⟩
  if h : twist.onCurve Q = true ∧ twist.mul r Q = .inf then some ⟨Q, h⟩ else none

/-- A `G1` point's 64 bytes. -/
def encodeG1 : Pt Fp → Bytes
  | .inf => word 0 ++ word 0
  | .aff x y => word x.val ++ word y.val

/-! ## The precompiles -/

def addGas (_ : Bytes) : Nat := 150

/-- `ECADD` (0x06). -/
def add (d : Bytes) : Option Bytes := do
  let P ← decodeG1 (readPad d 0 64)
  let Q ← decodeG1 (readPad d 64 64)
  some (encodeG1 (curve.add P.1 Q.1))

def mulGas (_ : Bytes) : Nat := 6000

/-- `ECMUL` (0x07). -/
def mul (d : Bytes) : Option Bytes := do
  let P ← decodeG1 (readPad d 0 64)
  some (encodeG1 (curve.mul (readNat d 64 32) P.1))

def pairingGas (d : Bytes) : Nat := 45000 + 34000 * (d.length / 192)

/-- One 192-byte pair of the pairing check, if well formed (`G1` in the
order-`r` subgroup too, which every point of BN254's `G1` is). -/
def decodePair (b : List Nat) : Option (G1 × G2) := do
  let P ← decodeG1 (b.take 64)
  if curve.mul r P.1 ≠ .inf then none
  let Q ← decodeG2 (b.drop 64)
  some (P, Q)

/-- The pairing check (0x08). -/
def pairing (d : Bytes) : Option Bytes := do
  if d.length % 192 ≠ 0 then none
  let pairs ← (chunks 192 (d.map UInt8.toNat)).mapM decodePair
  some (word (if pairingCurve.check (pairs.map fun pq => (pq.1.1, pq.2.1)) then 1 else 0))

/-! ## Failure cases -/

theorem add_eq_none_iff (d : Bytes) :
    add d = none ↔ decodeG1 (readPad d 0 64) = none ∨ decodeG1 (readPad d 64 64) = none := by
  simp only [add]
  cases decodeG1 (readPad d 0 64) <;> cases decodeG1 (readPad d 64 64) <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq, or_self, or_true, true_or,
      Option.bind_eq_bind]

theorem mul_eq_none_iff (d : Bytes) : mul d = none ↔ decodeG1 (readPad d 0 64) = none := by
  simp only [mul]
  cases decodeG1 (readPad d 0 64) <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq, Option.bind_eq_bind]

/-- The curve equation on coordinates: `y² = x³ + 3` modulo `p`. -/
theorem onCurve_aff (x y : Fp) :
    curve.onCurve (.aff x y) = decide (y.val * y.val % p = (x.val * x.val * x.val + 3) % p) := by
  show decide (y * y = x * x * x + 0 * x + 3) = decide (y.val * y.val % p = (x.val * x.val * x.val + 3) % p)
  simp only [Fin.ext_iff, Fin.val_add, Fin.val_mul, Fin.val_zero, Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
  rw [Nat.mod_mod, Nat.mod_mul_mod, Nat.mod_add_mod]
  rfl

/-- `G1` decoding fails exactly on a coordinate at or above `p`, or a point
other than `(0, 0)` off the curve. -/
theorem decodeG1_eq_none_iff (b : List Nat) :
    decodeG1 b = none ↔
      let x := ofBE (b.take 32)
      let y := ofBE ((b.drop 32).take 32)
      p ≤ x ∨ p ≤ y ∨ ¬(x = 0 ∧ y = 0) ∧ y * y % p ≠ (x * x * x + 3) % p := by
  simp only [decodeG1, coord]
  by_cases hx : ofBE (b.take 32) < p
  · by_cases hy : ofBE ((b.drop 32).take 32) < p
    · simp only [hx, hy, dite_true, Option.bind_eq_bind, Option.bind_some]
      by_cases h0 : ofBE (b.take 32) = 0 ∧ ofBE ((b.drop 32).take 32) = 0
      · simp only [h0, and_self, if_true, Curve.onCurve, dite_true, reduceCtorEq, false_iff,
          not_true_eq_false, false_and, or_false]
        omega
      · simp only [h0, if_false, onCurve_aff, decide_eq_true_eq, not_false_eq_true, true_and]
        by_cases he : ofBE ((b.drop 32).take 32) * ofBE ((b.drop 32).take 32) % p =
            (ofBE (b.take 32) * ofBE (b.take 32) * ofBE (b.take 32) + 3) % p
        · simp only [he, dite_true, reduceCtorEq, false_iff, ne_eq, not_true_eq_false, or_false]
          omega
        · simp only [he, dite_false, ne_eq, not_false_eq_true, or_true]
    · simp only [hx, hy, dite_true, dite_false, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, true_iff]
      omega
  · simp only [hx, dite_false, Option.bind_eq_bind, Option.bind_none, true_iff]
    omega

/-- The pairing check fails exactly on a length that is not a multiple of
192 or a malformed pair. -/
theorem pairing_eq_none_iff (d : Bytes) :
    pairing d = none ↔ d.length % 192 ≠ 0 ∨
      ∃ b ∈ chunks 192 (d.map UInt8.toNat), decodePair b = none := by
  simp only [pairing]
  by_cases h : d.length % 192 = 0
  · simp only [h, ne_eq, not_true_eq_false, if_false, false_or]
    rw [← mapM_eq_none_iff]
    cases (chunks 192 (d.map UInt8.toNat)).mapM decodePair <;>
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq]
  · simp only [h, ne_eq, not_false_eq_true, if_true, true_or, iff_true]
    exact rfl

/-! ## Vectors (Osaka's execution specification) -/

#guard add (ofHex "0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002") == some (ofHex "030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4")
#guard add (ofHex "0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000217c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c") == some (ofHex "09f4ca411a3f52f4e0792fd9e792779856719215d3b32a762afe3d5b8c684af90d8ef3d795acd4b35d4366ab22e4ad335273aa59429e26929d0f64583474d9c8")
#guard add (ofHex "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000130644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45") == some (ofHex "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")
#guard add (ofHex "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002") == some (ofHex "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002")
#guard add (ofHex "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000003") == none
#guard add (ofHex "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd470000000000000000000000000000000000000000000000000000000000000000") == none
#guard mul (ofHex "000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002") == some (ofHex "030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4")
#guard mul (ofHex "17072b2ed3bb8d759a5325f477629386cb6fc6ecb801bd76983a6b86abffe078168ada6cd130dd52017bb54bfa19377aadfe3bf05d18f41b77809f7f60d4af9effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") == some (ofHex "1f6825bf43bbc8b5d6aa49c0d577a236b2dc82e129ab45f180b32c902861f6ad00abd6b2d338890e038da4624d8a57e498ab03711065282bf4e8bb46ee9f4194")
#guard mul (ofHex "0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000230644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001") == some (ofHex "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")
#guard mul (ofHex "000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002") == none
#guard pairing (ofHex "") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000001")
#guard pairing (ofHex "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa000000000000000000000000000000000000000000000000000000000000000130644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000001")
#guard pairing (ofHex "030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa000000000000000000000000000000000000000000000000000000000000000130644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad7927dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de15204bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000001")
#guard pairing (ofHex "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000000")
#guard pairing (ofHex "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7d") == none
#guard pairing (ofHex "000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000004") == none

end Solidity.Precompiles.Bn254
