import Solidity.Precompiles.Pairing
import Solidity.Precompiles.Bls12381Iso

/-!
# BLS12-381: the EIP-2537 precompiles (0x0b–0x11)

Prague's BLS12-381 operations, as Osaka's execution specification
(`bls12_381/*.py`) runs them:

| Address | Operation | Input | Gas |
|---|---|---|---|
| 0x0b | `G1ADD` | 256 bytes | 375 |
| 0x0c | `G1MSM` | `k ≥ 1` pairs of 160 | `k·12000·discount₁(k)/1000` |
| 0x0d | `G2ADD` | 512 bytes | 600 |
| 0x0e | `G2MSM` | `k ≥ 1` pairs of 288 | `k·22500·discount₂(k)/1000` |
| 0x0f | `PAIRING_CHECK` | `k ≥ 1` pairs of 384 | `32600·k + 37700` |
| 0x10 | `MAP_FP_TO_G1` | 64 bytes | 5500 |
| 0x11 | `MAP_FP2_TO_G2` | 128 bytes | 23800 |

- **Encoding.**  An `Fp` element is 64 big-endian bytes below `p` (so its
  top 16 bytes are zero); an `Fp2` element is `c₀` then `c₁`; a point is
  `x` then `y`, all zeros being infinity.  Any other length, a coordinate at
  or above `p`, a point off its curve, or (for the MSMs and the pairing) a
  point outside the order-`r` subgroup is malformed: the call halts
  exceptionally (`*_eq_none_iff`).
- **The maps** are RFC 9380's simplified SWU map to the isogenous curve,
  its isogeny (`Bls12381Iso.lean`) and cofactor clearing by the effective
  cofactor, written as the RFC's straight-line `map_to_curve_simple_swu`;
  any square root serves, since the sign is fixed by `sgn0`.
- **Gas** is a function of the length alone; the MSM discount tables are
  EIP-2537's.

The `#guard`s are vectors computed by the execution specification itself.
-/

namespace Solidity.Precompiles.Bls12381

open Solidity.Roadmap.Evm (Bytes)

/-- The base field's prime. -/
def p : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
/-- The group order. -/
def r : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

instance : NeZero p := ⟨by decide⟩

abbrev Fp := Fin p
abbrev F2 := Fp2 p

def f2 (c : Nat × Nat) : F2 := ⟨Fin.ofNat p c.1, Fin.ofNat p c.2⟩

/-- `G1`: `y² = x³ + 4`. -/
def curve1 : Curve Fp := ⟨0, 4⟩

/-- `G2`'s curve, the M-twist `y² = x³ + 4·(1 + u)`. -/
def curve2 : Curve F2 := ⟨FieldOps.zero, ⟨4, 4⟩⟩

/-- `w⁻¹ = w⁵ - w¹¹/2` in `Fp[w] / (w¹² - 2·w⁶ + 2)`. -/
def wInv : Fp12 p := Fp12.ofFn fun i =>
  if i.val = 5 then 1 else if i.val = 11 then Fin.ofNat p ((p - 1) / 2) else 0

/-- BLS12-381 for the pairing check: `w¹² = 2·w⁶ - 2`, `u = w⁶ - 1`, the
M-twist (`t_k = w^(-k)`) and the ate loop count `|x|`. -/
def pairingCurve : PairingCurve p where
  order := r
  g1 := curve1
  g2 := curve2
  k₆ := 2
  k₀ := p - 2
  ξ := 1
  t₁ := wInv
  t₂ := Fp12.mul 2 (p - 2) wInv wInv
  t₃ := Fp12.mul 2 (p - 2) wInv (Fp12.mul 2 (p - 2) wInv wInv)
  loop := 15132376222941642752
  frob := none

/-! ## Encoding -/

/-- A field element in 64 bytes, if below `p`. -/
def decodeFp (b : List Nat) : Option Fp :=
  let n := ofBE b
  if h : n < p then some ⟨n, h⟩ else none

def decodeFp2 (b : List Nat) : Option F2 := do
  let c₀ ← decodeFp (b.take 64)
  let c₁ ← decodeFp ((b.drop 64).take 64)
  some ⟨c₀, c₁⟩

/-- A decoded `G1` point: on the curve. -/
abbrev G1 := { P : Pt Fp // curve1.onCurve P = true }

/-- A decoded `G2` point: on the curve. -/
abbrev G2 := { Q : Pt F2 // curve2.onCurve Q = true }

def decodeG1 (b : List Nat) : Option G1 := do
  let x ← decodeFp (b.take 64)
  let y ← decodeFp ((b.drop 64).take 64)
  let P : Pt Fp := if x.val = 0 ∧ y.val = 0 then .inf else .aff x y
  if h : curve1.onCurve P = true then some ⟨P, h⟩ else none

def decodeG2 (b : List Nat) : Option G2 := do
  let x ← decodeFp2 (b.take 128)
  let y ← decodeFp2 ((b.drop 128).take 128)
  let Q : Pt F2 := if x.re.val = 0 ∧ x.im.val = 0 ∧ y.re.val = 0 ∧ y.im.val = 0 then .inf else .aff x y
  if h : curve2.onCurve Q = true then some ⟨Q, h⟩ else none

/-- A `G1` point that is also in the order-`r` subgroup. -/
def decodeG1Sub (b : List Nat) : Option G1 := do
  let P ← decodeG1 b
  if curve1.mul r P.1 = .inf then some P else none

def decodeG2Sub (b : List Nat) : Option G2 := do
  let Q ← decodeG2 b
  if curve2.mul r Q.1 = .inf then some Q else none

def encodeFp (x : Fp) : Bytes := toBE 64 x.val

def encodeG1 : Pt Fp → Bytes
  | .inf => toBE 128 0
  | .aff x y => encodeFp x ++ encodeFp y

def encodeG2 : Pt F2 → Bytes
  | .inf => toBE 256 0
  | .aff x y => encodeFp x.re ++ encodeFp x.im ++ encodeFp y.re ++ encodeFp y.im

/-! ## Addition and multi-scalar multiplication -/

def g1AddGas (_ : Bytes) : Nat := 375

/-- `G1ADD` (0x0b). -/
def g1Add (d : Bytes) : Option Bytes := do
  if d.length ≠ 256 then none
  let b := d.map UInt8.toNat
  let P ← decodeG1 (b.take 128)
  let Q ← decodeG1 (b.drop 128)
  some (encodeG1 (curve1.add P.1 Q.1))

def g2AddGas (_ : Bytes) : Nat := 600

/-- `G2ADD` (0x0d). -/
def g2Add (d : Bytes) : Option Bytes := do
  if d.length ≠ 512 then none
  let b := d.map UInt8.toNat
  let P ← decodeG2 (b.take 256)
  let Q ← decodeG2 (b.drop 256)
  some (encodeG2 (curve2.add P.1 Q.1))

/-- EIP-2537's `G1MSM` discounts for `k = 1 … 128` (per mille); 519 above. -/
def g1Discount : List Nat := [
  1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677, 673, 669,
  665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627, 625, 623, 621, 619,
  617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598, 596, 595, 593, 592, 591, 589,
  588, 586, 585, 584, 582, 581, 580, 579, 577, 576, 575, 574, 573, 572, 570, 569, 568, 567,
  566, 565, 564, 563, 562, 561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 551, 550, 549,
  548, 547, 547, 546, 545, 544, 543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534,
  533, 532, 532, 531, 530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520,
  520, 519]

/-- EIP-2537's `G2MSM` discounts for `k = 1 … 128` (per mille); 524 above. -/
def g2Discount : List Nat := [
  1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717, 711, 704,
  699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646, 643, 640, 637, 634,
  632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607, 606, 604, 602, 600, 598, 597,
  595, 593, 592, 590, 589, 587, 586, 584, 583, 582, 580, 579, 578, 576, 575, 574, 573, 571,
  570, 569, 568, 567, 566, 565, 563, 562, 561, 560, 559, 558, 557, 556, 555, 554, 553, 552,
  552, 551, 550, 549, 548, 547, 546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537,
  537, 536, 535, 535, 534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525,
  524, 524]

theorem g1Discount_length : g1Discount.length = 128 := rfl
theorem g2Discount_length : g2Discount.length = 128 := rfl

/-- The MSM gas of `k` pairs with base cost `c`, the discount table and its
cap. -/
def msmGas (c : Nat) (table : List Nat) (cap k : Nat) : Nat :=
  k * c * (if k = 0 then 0 else table.getD (k - 1) cap) / 1000

def g1MsmGas (d : Bytes) : Nat := msmGas 12000 g1Discount 519 (d.length / 160)

def g2MsmGas (d : Bytes) : Nat := msmGas 22500 g2Discount 524 (d.length / 288)

/-- `G1MSM` (0x0c). -/
def g1Msm (d : Bytes) : Option Bytes := do
  if d.length = 0 ∨ d.length % 160 ≠ 0 then none
  let terms ← (chunks 160 (d.map UInt8.toNat)).mapM fun c => do
    let P ← decodeG1Sub (c.take 128)
    some (curve1.mul (ofBE (c.drop 128)) P.1)
  some (encodeG1 (terms.foldl curve1.add .inf))

/-- `G2MSM` (0x0e). -/
def g2Msm (d : Bytes) : Option Bytes := do
  if d.length = 0 ∨ d.length % 288 ≠ 0 then none
  let terms ← (chunks 288 (d.map UInt8.toNat)).mapM fun c => do
    let Q ← decodeG2Sub (c.take 256)
    some (curve2.mul (ofBE (c.drop 256)) Q.1)
  some (encodeG2 (terms.foldl curve2.add .inf))

/-! ## The pairing check -/

def pairingGas (d : Bytes) : Nat := 32600 * (d.length / 384) + 37700

/-- `PAIRING_CHECK` (0x0f). -/
def pairing (d : Bytes) : Option Bytes := do
  if d.length = 0 ∨ d.length % 384 ≠ 0 then none
  let pairs ← (chunks 384 (d.map UInt8.toNat)).mapM fun c => do
    let P ← decodeG1Sub (c.take 128)
    let Q ← decodeG2Sub (c.drop 128)
    some (P.1, Q.1)
  some (word (if pairingCurve.check pairs then 1 else 0))

/-! ## Mapping to the curves (RFC 9380) -/

/-- A square root in `Fp` (`p ≡ 3 mod 4`), if one exists. -/
def sqrtFp (a : Fp) : Option Fp :=
  let c := FieldOps.pow a ((p + 1) / 4)
  if c * c = a then some c else none

/-- A square root in `Fp2` (Adj and Rodríguez-Henríquez, algorithm 9, for
`p ≡ 3 mod 4`), if one exists. -/
def sqrtFp2 (a : F2) : Option F2 :=
  let a₁ := FieldOps.pow a ((p - 3) / 4)
  let α := a₁ * (a₁ * a)
  let x₀ := a₁ * a
  let x : F2 :=
    if α = -FieldOps.one then ⟨0, 1⟩ * x₀ else FieldOps.pow (FieldOps.one + α) ((p - 1) / 2) * x₀
  if x * x = a then some x else none

/-- RFC 9380's `sgn0`. -/
def sgn0Fp (a : Fp) : Bool := a.val % 2 = 1

def sgn0Fp2 (a : F2) : Bool := a.re.val % 2 = 1 || (a.re.val = 0 && a.im.val % 2 = 1)

/-- RFC 9380's `map_to_curve_simple_swu` onto `y² = x³ + A·x + B`, with
`Z`, the field's square root and `sgn0`. -/
def sswu {α : Type} [FieldOps α] [DecidableEq α] (A B Z : α) (sqrt : α → Option α)
    (sgn0 : α → Bool) (u : α) : α × α :=
  let g (x : α) : α := x * x * x + A * x + B
  let tv := Z * Z * (u * u) * (u * u) + Z * (u * u)
  let x₁ := if tv = FieldOps.zero then B * FieldOps.inv (Z * A)
    else -B * FieldOps.inv A * (FieldOps.one + FieldOps.inv tv)
  let (x, y) := match sqrt (g x₁) with
    | some y => (x₁, y)
    | none =>
      let x₂ := Z * (u * u) * x₁
      (x₂, (sqrt (g x₂)).getD FieldOps.zero)
  (x, if sgn0 u = sgn0 y then y else -y)

/-- A polynomial with coefficients lowest degree first, at `x` (Horner). -/
def poly {α : Type} [FieldOps α] (cs : List α) (x : α) : α :=
  cs.foldr (fun c acc => acc * x + c) FieldOps.zero

/-- RFC 9380's isogeny map: `(x_num/x_den, y·y_num/y_den)`, infinity on a
vanishing denominator. -/
def isoMap {α : Type} [FieldOps α] [DecidableEq α] (xn xd yn yd : List α) (pt : α × α) : Pt α :=
  let dx := poly xd pt.1
  let dy := poly yd pt.1
  if dx = FieldOps.zero ∨ dy = FieldOps.zero then .inf
  else .aff (poly xn pt.1 * FieldOps.inv dx) (pt.2 * poly yn pt.1 * FieldOps.inv dy)

/-- `G1`'s effective cofactor. -/
def hEff1 : Nat := 0xd201000000010001

def mapToG1 (u : Fp) : Pt Fp :=
  let c := Iso.iso11XNum.map (Fin.ofNat p)
  curve1.mul hEff1 <| isoMap c (Iso.iso11XDen.map (Fin.ofNat p)) (Iso.iso11YNum.map (Fin.ofNat p))
    (Iso.iso11YDen.map (Fin.ofNat p))
    (sswu (Fin.ofNat p Iso.iso11A) (Fin.ofNat p Iso.iso11B) (Fin.ofNat p 11) sqrtFp sgn0Fp u)

def mapToG2 (u : F2) : Pt F2 :=
  curve2.mul Iso.hEffG2 <| isoMap (Iso.iso3XNum.map f2) (Iso.iso3XDen.map f2) (Iso.iso3YNum.map f2)
    (Iso.iso3YDen.map f2) (sswu (f2 Iso.iso3A) (f2 Iso.iso3B) (f2 Iso.iso3Z) sqrtFp2 sgn0Fp2 u)

def mapFpToG1Gas (_ : Bytes) : Nat := 5500

/-- `MAP_FP_TO_G1` (0x10). -/
def mapFpToG1 (d : Bytes) : Option Bytes := do
  if d.length ≠ 64 then none
  let u ← decodeFp (d.map UInt8.toNat)
  some (encodeG1 (mapToG1 u))

def mapFp2ToG2Gas (_ : Bytes) : Nat := 23800

/-- `MAP_FP2_TO_G2` (0x11). -/
def mapFp2ToG2 (d : Bytes) : Option Bytes := do
  if d.length ≠ 128 then none
  let u ← decodeFp2 (d.map UInt8.toNat)
  some (encodeG2 (mapToG2 u))

/-! ## Failure cases and gas -/

theorem decodeFp_eq_none_iff (b : List Nat) : decodeFp b = none ↔ p ≤ ofBE b := by
  unfold decodeFp
  by_cases h : ofBE b < p
  · simp only [h, dite_true, reduceCtorEq, false_iff]
    omega
  · simp only [h, dite_false, true_iff]
    omega

theorem g1Add_eq_none_iff (d : Bytes) :
    g1Add d = none ↔ d.length ≠ 256 ∨ decodeG1 ((d.map UInt8.toNat).take 128) = none ∨
      decodeG1 ((d.map UInt8.toNat).drop 128) = none := by
  unfold g1Add
  by_cases h : d.length = 256
  · simp only [h, ne_eq, not_true_eq_false, if_false, false_or]
    cases decodeG1 ((d.map UInt8.toNat).take 128) <;> cases decodeG1 ((d.map UInt8.toNat).drop 128) <;>
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none,
        reduceCtorEq, or_self, or_true, true_or]
  · simp only [h, ne_eq, not_false_eq_true, if_true, true_or, iff_true]
    exact rfl

theorem g2Add_eq_none_iff (d : Bytes) :
    g2Add d = none ↔ d.length ≠ 512 ∨ decodeG2 ((d.map UInt8.toNat).take 256) = none ∨
      decodeG2 ((d.map UInt8.toNat).drop 256) = none := by
  unfold g2Add
  by_cases h : d.length = 512
  · simp only [h, ne_eq, not_true_eq_false, if_false, false_or]
    cases decodeG2 ((d.map UInt8.toNat).take 256) <;> cases decodeG2 ((d.map UInt8.toNat).drop 256) <;>
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none,
        reduceCtorEq, or_self, or_true, true_or]
  · simp only [h, ne_eq, not_false_eq_true, if_true, true_or, iff_true]
    exact rfl

/-- A `do` block that decodes then returns fails exactly when the decoding
does. -/
theorem bind_some_eq_none {α β : Type} (o : Option α) (f : α → β) :
    (do let a ← o; some (f a)) = none ↔ o = none := by
  cases o <;> simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq]

theorem g1Msm_eq_none_iff (d : Bytes) :
    g1Msm d = none ↔ d.length = 0 ∨ d.length % 160 ≠ 0 ∨
      ∃ c ∈ chunks 160 (d.map UInt8.toNat), decodeG1Sub (c.take 128) = none := by
  unfold g1Msm
  by_cases h : d.length = 0 ∨ d.length % 160 ≠ 0
  · simp only [h, if_true]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp only [h, if_false]
    have h' : ¬(d.length = 0 ∨ d.length % 160 ≠ 0) := h
    rw [← or_assoc, or_iff_right h']
    refine (bind_some_eq_none _ _).trans ?_
    rw [mapM_eq_none_iff]
    simp only [bind_some_eq_none]

theorem g2Msm_eq_none_iff (d : Bytes) :
    g2Msm d = none ↔ d.length = 0 ∨ d.length % 288 ≠ 0 ∨
      ∃ c ∈ chunks 288 (d.map UInt8.toNat), decodeG2Sub (c.take 256) = none := by
  unfold g2Msm
  by_cases h : d.length = 0 ∨ d.length % 288 ≠ 0
  · simp only [h, if_true]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp only [h, if_false]
    have h' : ¬(d.length = 0 ∨ d.length % 288 ≠ 0) := h
    rw [← or_assoc, or_iff_right h']
    refine (bind_some_eq_none _ _).trans ?_
    rw [mapM_eq_none_iff]
    simp only [bind_some_eq_none]

/-- One pair of the pairing check decodes exactly when both points do. -/
theorem pair_eq_none (c : List Nat) :
    (do let P ← decodeG1Sub (c.take 128); let Q ← decodeG2Sub (c.drop 128); some (P.1, Q.1)) = none ↔
      decodeG1Sub (c.take 128) = none ∨ decodeG2Sub (c.drop 128) = none := by
  cases decodeG1Sub (c.take 128) <;> cases decodeG2Sub (c.drop 128) <;>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq, or_self,
      or_true, true_or]

theorem pairing_eq_none_iff (d : Bytes) :
    pairing d = none ↔ d.length = 0 ∨ d.length % 384 ≠ 0 ∨
      ∃ c ∈ chunks 384 (d.map UInt8.toNat),
        decodeG1Sub (c.take 128) = none ∨ decodeG2Sub (c.drop 128) = none := by
  unfold pairing
  by_cases h : d.length = 0 ∨ d.length % 384 ≠ 0
  · simp only [h, if_true]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp only [h, if_false]
    have h' : ¬(d.length = 0 ∨ d.length % 384 ≠ 0) := h
    rw [← or_assoc, or_iff_right h']
    refine (bind_some_eq_none _ _).trans ?_
    rw [mapM_eq_none_iff]
    simp only [pair_eq_none]

/-- The MSM gas grows with the number of pairs. -/
theorem msmGas_succ (c : Nat) (table : List Nat) (cap k : Nat) (hlen : table.length = 128)
    (htab : ∀ i < 128, (i + 1) * table.getD i cap ≤ (i + 2) * table.getD (i + 1) cap) :
    msmGas c table cap k ≤ msmGas c table cap (k + 1) := by
  unfold msmGas
  apply Nat.div_le_div_right
  cases k with
  | zero => simp only [Nat.zero_mul, if_true, Nat.zero_le]
  | succ k =>
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases hk : k < 128
    · have h1 := Nat.mul_le_mul_left c (htab k hk)
      rw [Nat.mul_comm (k + 1) c, Nat.mul_comm (k + 1 + 1) c, Nat.mul_assoc, Nat.mul_assoc]
      exact h1
    · have e1 : table.getD k cap = cap := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : table.length ≤ k),
          Option.getD_none]
      have e2 : table.getD (k + 1) cap = cap := by
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega : table.length ≤ k + 1), Option.getD_none]
      rw [e1, e2]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem msmGas_mono (c : Nat) (table : List Nat) (cap : Nat) (hlen : table.length = 128)
    (htab : ∀ i < 128, (i + 1) * table.getD i cap ≤ (i + 2) * table.getD (i + 1) cap) {k l : Nat} (h : k ≤ l) :
    msmGas c table cap k ≤ msmGas c table cap l := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (msmGas_succ c table cap _ hlen htab)

theorem g1MsmGas_mono {d e : Bytes} (h : d.length ≤ e.length) : g1MsmGas d ≤ g1MsmGas e :=
  msmGas_mono 12000 g1Discount 519 rfl (by decide) (Nat.div_le_div_right h)

theorem g2MsmGas_mono {d e : Bytes} (h : d.length ≤ e.length) : g2MsmGas d ≤ g2MsmGas e :=
  msmGas_mono 22500 g2Discount 524 rfl (by decide) (Nat.div_le_div_right h)

theorem pairingGas_mono {d e : Bytes} (h : d.length ≤ e.length) : pairingGas d ≤ pairingGas e :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 32600 (Nat.div_le_div_right h)) 37700

theorem mapFpToG1_eq_none_iff (d : Bytes) :
    mapFpToG1 d = none ↔ d.length ≠ 64 ∨ p ≤ ofBE (d.map UInt8.toNat) := by
  unfold mapFpToG1
  by_cases h : d.length = 64
  · simp only [h, ne_eq, not_true_eq_false, if_false, false_or, ← decodeFp_eq_none_iff]
    exact bind_some_eq_none _ _
  · simp only [h, ne_eq, not_false_eq_true, if_true, true_or, iff_true]
    exact rfl

theorem decodeFp2_eq_none_iff (b : List Nat) :
    decodeFp2 b = none ↔ p ≤ ofBE (b.take 64) ∨ p ≤ ofBE ((b.drop 64).take 64) := by
  unfold decodeFp2
  rw [← decodeFp_eq_none_iff, ← decodeFp_eq_none_iff]
  cases decodeFp (b.take 64) <;> cases decodeFp ((b.drop 64).take 64) <;>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq, or_self,
      or_true, true_or]

theorem mapFp2ToG2_eq_none_iff (d : Bytes) :
    mapFp2ToG2 d = none ↔ d.length ≠ 128 ∨ decodeFp2 (d.map UInt8.toNat) = none := by
  unfold mapFp2ToG2
  by_cases h : d.length = 128
  · simp only [h, ne_eq, not_true_eq_false, if_false, false_or]
    exact bind_some_eq_none _ _
  · simp only [h, ne_eq, not_false_eq_true, if_true, true_or, iff_true]
    exact rfl

/-! ## Vectors (Osaka's execution specification) -/

#guard g1Add (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000009ece308f9d1f0131765212deca99697b112d61f9be9a5f1f3780a51335b3ff981747a0b2ca2179b96d2c0c9024e522400000000000000000000000000000000032b80d3a6f5b09f8a84623389c5f80ca69a0cddabc3097f9d9c27310fd43be6e745256c634af45ca3473b0590ae30d1") == some (ofHex "000000000000000000000000000000000c9b60d5afcbd5663a8a44b7c5a02f19e9a77ab0a35bd65809bb5c67ec582c897feb04decc694b13e08587f3ff9b5b6000000000000000000000000000000000143be6d078c2b79a7d4f1d1b21486a030ec93f56aa54e1de880db5a66dd833a652a95bee27c824084006cb5644cbd43f")
#guard g1AddGas (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000009ece308f9d1f0131765212deca99697b112d61f9be9a5f1f3780a51335b3ff981747a0b2ca2179b96d2c0c9024e522400000000000000000000000000000000032b80d3a6f5b09f8a84623389c5f80ca69a0cddabc3097f9d9c27310fd43be6e745256c634af45ca3473b0590ae30d1") == 375
#guard g1Add (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == some (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1")
#guard g1AddGas (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == 375
#guard g1Add (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")
#guard g1AddGas (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca") == 375
#guard g1Add (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7") == none
#guard g1Add (ofHex "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1") == none
#guard g2Add (ofHex "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be000000000000000000000000000000001638533957d540a9d2370f17cc7ed5863bc0b995b8825e0ee1ea1e1e4d00dbae81f14b0bf3611b78c952aacab827a053000000000000000000000000000000000a4edef9c1ed7f729f520e47730a124fd70662a904ba1074728114d1031e1572c6c886f6b57ec72a6178288c47c33577000000000000000000000000000000000468fb440d82b0630aeb8dca2b5256789a66da69bf91009cbfe6bd221e47aa8ae88dece9764bf3bd999d95d71e4c9899000000000000000000000000000000000f6d4552fa65dd2638b361543f887136a43253d9c66c411697003f7a13c308f5422e1aa0a59c8967acdefd8b6e36ccf3") == some (ofHex "00000000000000000000000000000000122915c824a0857e2ee414a3dccb23ae691ae54329781315a0c75df1c04d6d7a50a030fc866f09d516020ef82324afae0000000000000000000000000000000009380275bbc8e5dcea7dc4dd7e0550ff2ac480905396eda55062650f8d251c96eb480673937cc6d9d6a44aaa56ca66dc000000000000000000000000000000000b21da7955969e61010c7a1abc1a6f0136961d1e3b20b1a7326ac738fef5c721479dfd948b52fdf2455e44813ecfd8920000000000000000000000000000000008f239ba329b3967fe48d718a36cfe5f62a7e42e0bf1c1ed714150a166bfbd6bcf6b3b58b975b9edea56d53f23a0e849")
#guard g2AddGas (ofHex "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be000000000000000000000000000000001638533957d540a9d2370f17cc7ed5863bc0b995b8825e0ee1ea1e1e4d00dbae81f14b0bf3611b78c952aacab827a053000000000000000000000000000000000a4edef9c1ed7f729f520e47730a124fd70662a904ba1074728114d1031e1572c6c886f6b57ec72a6178288c47c33577000000000000000000000000000000000468fb440d82b0630aeb8dca2b5256789a66da69bf91009cbfe6bd221e47aa8ae88dece9764bf3bd999d95d71e4c9899000000000000000000000000000000000f6d4552fa65dd2638b361543f887136a43253d9c66c411697003f7a13c308f5422e1aa0a59c8967acdefd8b6e36ccf3") == 600
#guard g2Add (ofHex "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == some (ofHex "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be")
#guard g2AddGas (ofHex "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == 600
#guard g1Msm (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000005") == some (ofHex "0000000000000000000000000000000010e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc0000000000000000000000000000000016ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e2")
#guard g1MsmGas (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000005") == 12000
#guard g1Msm (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000001928f3beb93519eecf0145da903b40a4c97dca00b21f12ac0df3be9116ef2ef27b2ae6bcd4c5bc2d54ef5a70627efcb700000000000000000000000000000000108dadbaa4b636445639d5ae3089b3c43a8a1d47818edd1839d7383959a41c10fdc66849cfa1b08c5a11ec7e28981a1c0000000000000000000000000000000000000000000000000000000000000003") == some (ofHex "000000000000000000000000000000000c8b694b04d98a749a0763c72fc020ef61b2bb3f63ebb182cb2e568f6a8b9ca3ae013ae78317599e7e7ba2a528ec754a000000000000000000000000000000000951b70c206350e1edc2aefdfaa95318368c151e01e468b9fb1cf7c3c6575e4f06c135715cc5e51e1b492d19adf9bee0")
#guard g1MsmGas (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000001928f3beb93519eecf0145da903b40a4c97dca00b21f12ac0df3be9116ef2ef27b2ae6bcd4c5bc2d54ef5a70627efcb700000000000000000000000000000000108dadbaa4b636445639d5ae3089b3c43a8a1d47818edd1839d7383959a41c10fdc66849cfa1b08c5a11ec7e28981a1c0000000000000000000000000000000000000000000000000000000000000003") == 22776
#guard g1Msm (ofHex "") == none
#guard g1Msm (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1000000000000000000000000000000000000000000000000000000000000000500") == none
#guard g2Msm (ofHex "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000005") == some (ofHex "000000000000000000000000000000000411a5de6730ffece671a9f21d65028cc0f1102378de124562cb1ff49db6f004fcd14d683024b0548eff3d1468df26880000000000000000000000000000000000fb837804dba8213329db46608b6c121d973363c1234a86dd183baff112709cf97096c5e9a1a770ee9d7dc641a894d60000000000000000000000000000000019b5e8f5d4a72f2b75811ac084a7f814317360bac52f6aab15eed416b4ef9938e0bdc4865cc2c4d0fd947e7c6925fd1400000000000000000000000000000000093567b4228be17ee62d11a254edd041ee4b953bffb8b8c7f925bd6662b4298bac2822b446f5b5de3b893e1be5aa4986")
#guard g2MsmGas (ofHex "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000005") == 22500
#guard pairing (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000001")
#guard pairingGas (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be") == 102900
#guard pairing (ofHex "000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d2800000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca000000000000000000000000000000001638533957d540a9d2370f17cc7ed5863bc0b995b8825e0ee1ea1e1e4d00dbae81f14b0bf3611b78c952aacab827a053000000000000000000000000000000000a4edef9c1ed7f729f520e47730a124fd70662a904ba1074728114d1031e1572c6c886f6b57ec72a6178288c47c33577000000000000000000000000000000000468fb440d82b0630aeb8dca2b5256789a66da69bf91009cbfe6bd221e47aa8ae88dece9764bf3bd999d95d71e4c9899000000000000000000000000000000000f6d4552fa65dd2638b361543f887136a43253d9c66c411697003f7a13c308f5422e1aa0a59c8967acdefd8b6e36ccf3") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000001")
#guard pairingGas (ofHex "000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d2800000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca000000000000000000000000000000001638533957d540a9d2370f17cc7ed5863bc0b995b8825e0ee1ea1e1e4d00dbae81f14b0bf3611b78c952aacab827a053000000000000000000000000000000000a4edef9c1ed7f729f520e47730a124fd70662a904ba1074728114d1031e1572c6c886f6b57ec72a6178288c47c33577000000000000000000000000000000000468fb440d82b0630aeb8dca2b5256789a66da69bf91009cbfe6bd221e47aa8ae88dece9764bf3bd999d95d71e4c9899000000000000000000000000000000000f6d4552fa65dd2638b361543f887136a43253d9c66c411697003f7a13c308f5422e1aa0a59c8967acdefd8b6e36ccf3") == 102900
#guard pairing (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be") == some (ofHex "0000000000000000000000000000000000000000000000000000000000000000")
#guard pairingGas (ofHex "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be") == 70300
#guard pairing (ofHex "") == none
#guard mapFpToG1 (ofHex "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == some (ofHex "0000000000000000000000000000000011a9a0372b8f332d5c30de9ad14e50372a73fa4c45d5f2fa5097f2d6fb93bcac592f2e1711ac43db0519870c7d0ea41500000000000000000000000000000000092c0f994164a0719f51c24ba3788de240ff926b55f58c445116e8bc6a47cd63392fd4e8e22bdf9feaa96ee773222133")
#guard mapFpToG1Gas (ofHex "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == 5500
#guard mapFpToG1 (ofHex "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001") == some (ofHex "000000000000000000000000000000001073311196f8ef19477219ccee3a48035ff432295aa9419eed45d186027d88b90832e14c4f0e2aa4d15f54d1c3ed0f9300000000000000000000000000000000034d6e3755a2073039d609db4cf3aef548283b5cc92f1021cbdb276414bcd8072b112d80a2b0a7dbf22bdaf17e006d45")
#guard mapFpToG1Gas (ofHex "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001") == 5500
#guard mapFpToG1 (ofHex "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000075bcd15") == some (ofHex "0000000000000000000000000000000013e0389e420f134a77d24f520b6ff40db8b6fe19137462ec777c5b28dfda6fb7453510991fd7aeda186fa45c1d7d08e7000000000000000000000000000000000328ba308b2ed6a8dde4cd8ddddd3e993a02626412c15538e217f960265fc082e73254f9bd78f970061cfc1b17ebacc4")
#guard mapFpToG1Gas (ofHex "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000075bcd15") == 5500
#guard mapFpToG1 (ofHex "000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab") == none
#guard mapFpToG1 (ofHex "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == none
#guard mapFp2ToG2 (ofHex "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == some (ofHex "00000000000000000000000000000000018320896ec9eef9d5e619848dc29ce266f413d02dd31d9b9d44ec0c79cd61f18b075ddba6d7bd20b7ff27a4b324bfce000000000000000000000000000000000a67d12118b5a35bb02d2e86b3ebfa7e23410db93de39fb06d7025fa95e96ffa428a7a27c3ae4dd4b40bd251ac658892000000000000000000000000000000000260e03644d1a2c321256b3246bad2b895cad13890cbe6f85df55106a0d334604fb143c7a042d878006271865bc359410000000000000000000000000000000004c69777a43f0bda07679d5805e63f18cf4e0e7c6112ac7f70266d199b4f76ae27c6269a3ceebdae30806e9a76aadf5c")
#guard mapFp2ToG2Gas (ofHex "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == 23800
#guard mapFp2ToG2 (ofHex "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002") == some (ofHex "0000000000000000000000000000000003affe41434a0ba0c57a12a44659cb0a3880ab68671d59e14ada0697e1e284a24bbd1027e73fb2a5fa1b7b83a2ee3693000000000000000000000000000000000afb7419b48cf4b1d4205cb7a65b76bb00da7a3bdfa1b8da5bfda384aa78e27dbe4838d2660c885c80845e83ff4eea300000000000000000000000000000000016472687b24e83cbb72b626b04f37e880ff22701500ab276f7a553cd95315b06f39f8f21218aabc3367aeca0152322e8000000000000000000000000000000000a17e8006aa32586025a73fb9f5147067aeec10241a8eca8d8e2f121cf18080cfb0618c528d92a5ad538c7ffcf46d81f")
#guard mapFp2ToG2Gas (ofHex "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002") == 23800
#guard mapFp2ToG2 (ofHex "000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == none


end Solidity.Precompiles.Bls12381
