import Solidity.Language.FixedPoint.Laws

/-!
# Fixed-point literals and constants

Rational constants fold exactly, as solc's `ConstantEvaluator` does: a
constant expression evaluates to a `Rat` (Lean core's normalized rationals),
with solc's compile errors (a zero divisor, a non-integer exponent, the
4096-bit precision bound) as `none` (`CExpr.eval`).  A constant meets a
fixed-point type in four ways (`docs/feature-work/fixed-point-semantics.md`,
§6.2):

* an implicit conversion, exact and in range or a compile error
  (`Fx.ofRat?`; `Fx.ofLiteral?_isSome_iff_solc`: exactly solc's test);
* an explicit conversion, folded at the target's digits and truncated
  toward zero, a compile error when out of range (`Fx.explicitRat?`, Q2, P1);
* the mobile type a fractional constant takes when it needs a type of its
  own (`mobileFx?`, solc's `RationalNumberType::fixedPointType`), which
  holds the constant truncated toward zero (`mobileFx?_inRange`) and holds
  it exactly if and only if its digits suffice (`mobileFx?_exact`);
* the common type of a fixed-point operand and a constant operand:
  `x op c` (`litCommon?`) is solc's `Type::commonType` restricted, as Q1
  requires, to pairs where the constant converts exactly
  (`litCommon?_solc`); `c op x` (`litCommonRev?`) is solc's rule, which
  refuses a fractional `c` (`litCommonRev?_eq_solc`).

Only the rational value of a constant matters, not its spelling
(`Fx.ofLiteral?_congr`, `Fx.literalTrunc_congr`).
-/

namespace Solidity.Language.FixedPoint

/-! ### Constant expressions -/

/-- solc's bound on a folded constant: numerator and denominator of at most
4096 bits (`RationalNumberType::binaryOperatorResult`, "Precision of rational
constants is limited to 4096 bits"). -/
def fitsPrecision (q : Rat) : Bool :=
  q.num == 0 || (decide (q.num.natAbs.log2 ≤ 4096) && decide (q.den.log2 ≤ 4096))

/-- solc's `fitsPrecisionExp`: whether `base ^ e` may fit into 4096 bits,
checked before a power is computed. -/
def fitsPrecisionExp (base e : Nat) : Bool :=
  base == 0 || base.log2 == 0 || (decide (base.log2 ≤ 4096) && decide (e * (base.log2 + 1) ≤ 4096))

/-- A rational constant expression: literals and the operators solc folds on
rationals that fixed-point code can use (no bit operators or shifts, which
fail on fractional constants). -/
inductive CExpr where
  | lit (q : Rat)
  | neg (a : CExpr)
  | add (a b : CExpr)
  | sub (a b : CExpr)
  | mul (a b : CExpr)
  | div (a b : CExpr)
  | mod (a b : CExpr)
  | pow (a b : CExpr)

/-- The truncated integer quotient of a rational. -/
def ratTrunc (q : Rat) : Int := q.num.tdiv q.den

/-- A folded result, refused beyond the precision bound. -/
def precise (q : Rat) : Option Rat := if fitsPrecision q then some q else none

/-- A power `p ** k` with an integer exponent, as `evaluateBinaryOperator`:
`0`, `1` and `-1` bases and a zero exponent skip the pre-checks (solc
returns them early; the later 4096-bit check always passes for them);
otherwise the exponent must fit in 32 bits and the pre-check must pass. -/
def ratPow (p : Rat) (k : Int) : Option Rat :=
  if k = 0 ∨ p = 0 ∨ p = 1 ∨ p = -1 then precise (p ^ k)
  else if k.natAbs ≤ 2 ^ 32 - 1 ∧ fitsPrecisionExp p.num.natAbs k.natAbs = true ∧
      fitsPrecisionExp p.den k.natAbs = true then precise (p ^ k)
  else none

/-- Exact folding (`ConstantEvaluator::evaluateBinaryOperator`): `none` is a
compile error. -/
def CExpr.eval : CExpr → Option Rat
  | .lit q => some q
  | .neg a => (eval a).map (- ·)
  | .add a b => do precise ((← eval a) + (← eval b))
  | .sub a b => do precise ((← eval a) - (← eval b))
  | .mul a b => do precise ((← eval a) * (← eval b))
  | .div a b => do
      let p ← eval a
      let r ← eval b
      if r = 0 then none else precise (p / r)
  | .mod a b => do
      let p ← eval a
      let r ← eval b
      if r = 0 then none else precise (p - (ratTrunc (p / r) : Rat) * r)
  | .pow a b => do
      let p ← eval a
      let r ← eval b
      if r.den = 1 then ratPow p r.num else none

/-! ### Implicit and explicit conversions of a constant -/

namespace Fx

variable {t : FxTy}

/-- An implicit conversion of a rational literal is the exact one. -/
theorem ofLiteral?_eq_some_iff {num : Int} {den : Nat} (hd : den ≠ 0) {a : Fx t} :
    ofLiteral? t num den = some a ↔ a.1 * den = num * t.scale := by
  have hd' : (den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr hd
  unfold ofLiteral?
  simp only [hd, if_false]
  by_cases hm : (num * t.scale) % (den : Int) = 0
  · have hdv : (den : Int) ∣ num * t.scale := Int.dvd_of_emod_eq_zero hm
    simp only [hm, if_true, ofInt?]
    constructor
    · intro h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Int.ediv_mul_cancel hdv
      · exact nomatch h
    · intro h
      have he : num * t.scale / den = a.1 := by
        rw [← h]; exact Int.mul_ediv_cancel a.1 hd'
      have hr : t.inRange (num * t.scale / den) = true := by rw [he]; exact a.2
      simp only [hr, dite_true, Option.some.injEq]
      exact Subtype.ext he
  · simp only [hm, if_false]
    constructor
    · intro h; exact nomatch h
    · intro h
      have hz : (num * t.scale) % (den : Int) = 0 := by rw [← h]; exact Int.mul_emod_left a.1 den
      exact absurd hz hm

/-- Only the value of a literal matters: two spellings `n₁/d₁ = n₂/d₂`
convert alike. -/
theorem ofLiteral?_congr {n₁ n₂ : Int} {d₁ d₂ : Nat} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (he : n₁ * d₂ = n₂ * d₁) : ofLiteral? t n₁ d₁ = ofLiteral? t n₂ d₂ := by
  have hp₁ : (0 : Int) < d₁ := Int.natCast_pos.mpr (Nat.pos_of_ne_zero h₁)
  have hp₂ : (0 : Int) < d₂ := Int.natCast_pos.mpr (Nat.pos_of_ne_zero h₂)
  have key : ∀ a : Fx t, a.1 * d₁ = n₁ * t.scale ↔ a.1 * d₂ = n₂ * t.scale := by
    intro a
    constructor
    · intro h
      apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hp₁)
      calc a.1 * d₂ * d₁ = a.1 * d₁ * d₂ := by rw [Int.mul_right_comm]
        _ = n₁ * t.scale * d₂ := by rw [h]
        _ = n₁ * d₂ * t.scale := by rw [Int.mul_right_comm]
        _ = n₂ * d₁ * t.scale := by rw [he]
        _ = n₂ * t.scale * d₁ := by rw [Int.mul_right_comm]
    · intro h
      apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hp₂)
      calc a.1 * d₁ * d₂ = a.1 * d₂ * d₁ := by rw [Int.mul_right_comm]
        _ = n₂ * t.scale * d₁ := by rw [h]
        _ = n₂ * d₁ * t.scale := by rw [Int.mul_right_comm]
        _ = n₁ * d₂ * t.scale := by rw [he]
        _ = n₁ * t.scale * d₂ := by rw [Int.mul_right_comm]
  cases h₁' : ofLiteral? t n₁ d₁ with
  | none =>
    cases h₂' : ofLiteral? t n₂ d₂ with
    | none => rfl
    | some b =>
      have hb : b.1 * d₁ = n₁ * t.scale := (key b).mpr ((ofLiteral?_eq_some_iff h₂).mp h₂')
      rw [(ofLiteral?_eq_some_iff h₁).mpr hb] at h₁'
      exact nomatch h₁'
  | some a =>
    have ha : a.1 * d₂ = n₂ * t.scale := (key a).mp ((ofLiteral?_eq_some_iff h₁).mp h₁')
    exact ((ofLiteral?_eq_some_iff h₂).mpr ha).symm

/-- The truncated scaled integer depends only on the value. -/
theorem literalTrunc_congr {n₁ n₂ : Int} {d₁ d₂ : Nat} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (he : n₁ * d₂ = n₂ * d₁) : literalTrunc t n₁ d₁ = literalTrunc t n₂ d₂ := by
  have hp₁ : (0 : Int) < d₁ := Int.natCast_pos.mpr (Nat.pos_of_ne_zero h₁)
  have hp₂ : (0 : Int) < d₂ := Int.natCast_pos.mpr (Nat.pos_of_ne_zero h₂)
  unfold literalTrunc
  have e1 : (n₁ * t.scale).tdiv d₁ = (n₁ * t.scale * d₂).tdiv (d₁ * d₂) := by
    rw [Int.mul_tdiv_mul_of_pos_left _ _ hp₂]
  have e2 : (n₂ * t.scale).tdiv d₂ = (n₂ * t.scale * d₁).tdiv (d₂ * d₁) := by
    rw [Int.mul_tdiv_mul_of_pos_left _ _ hp₁]
  have e3 : n₁ * t.scale * d₂ = n₂ * t.scale * d₁ := by
    rw [Int.mul_right_comm, he, Int.mul_right_comm]
  rw [e1, e2, e3, Int.mul_comm (d₁ : Int)]

/-- An implicit conversion of a rational constant. -/
def ofRat? (t : FxTy) (q : Rat) : Option (Fx t) := ofLiteral? t q.num q.den

/-- An explicit conversion of a rational constant: folded exactly at the
target's digits, truncated toward zero, a compile error out of range. -/
def explicitRat? (t : FxTy) (q : Rat) : Option (Fx t) := explicitConst? t q.num q.den

/-- A literal written `n / d` converts as its value. -/
theorem ofRat?_mkRat {n : Int} {d : Nat} (hd : d ≠ 0) :
    ofRat? t (mkRat n d) = ofLiteral? t n d := by
  have hq : mkRat (mkRat n d).num (mkRat n d).den = mkRat n d := Rat.mkRat_self _
  have he : (mkRat n d).num * d = n * (mkRat n d).den :=
    (Rat.mkRat_eq_iff (mkRat n d).den_nz hd).mp hq
  exact ofLiteral?_congr (mkRat n d).den_nz hd he

theorem ofRat?_eq_some_iff {q : Rat} {a : Fx t} :
    ofRat? t q = some a ↔ a.1 * q.den = q.num * t.scale :=
  ofLiteral?_eq_some_iff q.den_nz

/-- An explicit conversion of a constant is its truncated scaled integer. -/
theorem explicitConst?_eq_some_iff {num : Int} {den : Nat} (hd : den ≠ 0) {a : Fx t} :
    explicitConst? t num den = some a ↔ a.1 = literalTrunc t num den := by
  unfold explicitConst? ofInt?
  simp only [hd, if_false]
  constructor
  · intro h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · exact nomatch h
  · intro h
    have hr : t.inRange (literalTrunc t num den) = true := by rw [← h]; exact a.2
    simp only [hr, dite_true, Option.some.injEq]
    exact Subtype.ext h.symm

/-- An explicit conversion of a constant is a compile error exactly when
the truncated value is out of range (Q2). -/
theorem explicitConst?_eq_none_iff {num : Int} {den : Nat} (hd : den ≠ 0) :
    explicitConst? t num den = none ↔ t.inRange (literalTrunc t num den) = false := by
  unfold explicitConst? ofInt?
  simp only [hd, if_false]
  constructor
  · intro h
    split at h
    · exact nomatch h
    · rename_i hn
      simp only [Bool.not_eq_true] at hn
      exact hn
  · intro h
    simp only [h, Bool.false_eq_true, dite_false]

/-- Where the implicit conversion exists, the explicit one is it. -/
theorem explicitConst?_of_ofLiteral? {num : Int} {den : Nat} (hd : den ≠ 0) {a : Fx t}
    (h : ofLiteral? t num den = some a) : explicitConst? t num den = some a := by
  have he : a.1 * den = num * t.scale := (ofLiteral?_eq_some_iff hd).mp h
  have hdv : (den : Int) ∣ num * t.scale := ⟨a.1, by rw [← he, Int.mul_comm]⟩
  have hp : (den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr hd
  apply (explicitConst?_eq_some_iff hd).mpr
  unfold literalTrunc
  rw [← he]
  exact (Int.mul_tdiv_cancel a.1 hp).symm

/-- An explicit conversion of a constant truncates toward zero: `a·d`
lies between `0` and `num·10^N`, less than one `d` away. -/
theorem explicitConst?_trunc {num : Int} {den : Nat} (hd : den ≠ 0) {a : Fx t}
    (h : explicitConst? t num den = some a) :
    (0 ≤ num → 0 ≤ a.1 * den ∧ a.1 * den ≤ num * t.scale ∧ num * t.scale < a.1 * den + den) ∧
    (num < 0 → a.1 * den - den < num * t.scale ∧ num * t.scale ≤ a.1 * den ∧
      a.1 * den ≤ 0) := by
  have ha : a.1 = (num * t.scale).tdiv den := (explicitConst?_eq_some_iff hd).mp h
  have hp : (0 : Int) < den := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hd)
  have hs : 0 < t.scale := t.scale_pos
  have ht : (0 ≤ num * t.scale → 0 ≤ (num * t.scale).tdiv den * den ∧
      (num * t.scale).tdiv den * den ≤ num * t.scale ∧
      num * t.scale < (num * t.scale).tdiv den * den + den) ∧
    (num * t.scale < 0 → (num * t.scale).tdiv den * den - den < num * t.scale ∧
      num * t.scale ≤ (num * t.scale).tdiv den * den ∧ (num * t.scale).tdiv den * den ≤ 0) :=
    tdiv_trunc (num * t.scale) den hp
  rw [ha]
  refine ⟨fun hn => ht.1 (Int.mul_nonneg hn (by omega)),
    fun hn => ht.2 (Int.mul_neg_of_neg_of_pos hn hs)⟩

theorem explicitRat?_mkRat {n : Int} {d : Nat} (hd : d ≠ 0) :
    explicitRat? t (mkRat n d) = explicitConst? t n d := by
  have hq : mkRat (mkRat n d).num (mkRat n d).den = mkRat n d := Rat.mkRat_self _
  have he : (mkRat n d).num * d = n * (mkRat n d).den :=
    (Rat.mkRat_eq_iff (mkRat n d).den_nz hd).mp hq
  unfold explicitRat? explicitConst?
  simp only [(mkRat n d).den_nz, hd, if_false, literalTrunc_congr (mkRat n d).den_nz hd he]

/-! ### solc's implicit literal test -/

/-- solc's `RationalNumberType::isImplicitlyConvertibleTo` for a fixed-point
target: no negative value into `ufixed`; an integer by solc's integer-part
bounds; a fraction by an exact scaled integer that fits the bits. -/
def solcLiteralOK (t : FxTy) (num : Int) (den : Nat) : Bool :=
  if num < 0 ∧ t.signed = false then false
  else if num % den = 0 then decide (t.minInt ≤ num / den) && decide (num / den ≤ t.maxInt)
  else decide ((num * t.scale) % den = 0) && t.inRange ((num * t.scale) / den)

/-- The implicit conversion of a literal is exactly solc's. -/
theorem ofLiteral?_isSome_iff_solc {num : Int} {den : Nat} (hd : den ≠ 0) :
    (ofLiteral? t num den).isSome = solcLiteralOK t num den := by
  have hp : (0 : Int) < den := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hd)
  have hs : 0 < t.scale := t.scale_pos
  have hl : t.lo ≤ 0 := t.lo_le_zero
  have hh : 0 ≤ t.hi := t.hi_nonneg
  -- the implicit conversion as a test
  have hlit : (ofLiteral? t num den).isSome =
      (decide ((num * t.scale) % den = 0) && t.inRange ((num * t.scale) / den)) := by
    unfold ofLiteral? ofInt?
    simp only [hd, if_false]
    by_cases hm : (num * t.scale) % (den : Int) = 0
    · simp only [hm, if_true, decide_true, Bool.true_and]
      by_cases hr : t.inRange (num * t.scale / den) = true
      · simp only [hr, dite_true, Option.isSome_some]
      · simp only [hr, Bool.false_eq_true, dite_false, Option.isSome_none]
    · simp only [hm, if_false, decide_false, Bool.false_and, Option.isSome_none]
  rw [hlit]
  unfold solcLiteralOK
  by_cases hneg : num < 0 ∧ t.signed = false
  · simp only [hneg, and_self, if_true]
    -- a negative value is never in an unsigned range
    apply Bool.eq_false_iff.mpr
    intro hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hm, hr⟩ := hc
    have hdv : (den : Int) ∣ num * t.scale := Int.dvd_of_emod_eq_zero hm
    have hq : num * t.scale / den * den = num * t.scale := Int.ediv_mul_cancel hdv
    simp only [FxTy.inRange, FxTy.lo, hneg.2, Bool.false_eq_true, if_false, Bool.and_eq_true,
      decide_eq_true_eq] at hr
    have h1 : num * t.scale < 0 := Int.mul_neg_of_neg_of_pos hneg.1 hs
    have h2 : 0 ≤ num * t.scale / den * den := Int.mul_nonneg hr.1 (by omega)
    omega
  · simp only [hneg, if_false]
    by_cases hi : num % (den : Int) = 0
    · simp only [hi, if_true]
      have hdv : (den : Int) ∣ num := Int.dvd_of_emod_eq_zero hi
      obtain ⟨k, hk⟩ := hdv
      have hk' : num / den = k := by rw [hk]; exact Int.mul_ediv_cancel_left k (by omega)
      have hm : (num * t.scale) % (den : Int) = 0 := by
        rw [hk, Int.mul_assoc]; exact Int.mul_emod_right _ _
      have hq : num * t.scale / den = k * t.scale := by
        rw [hk, Int.mul_assoc]; exact Int.mul_ediv_cancel_left _ (by omega)
      simp only [hm, decide_true, Bool.true_and, hq, hk']
      -- `k·10^N` in range iff `k` within solc's integer-part bounds
      have hup : k * t.scale ≤ t.hi ↔ k ≤ t.maxInt := by
        simp only [FxTy.maxInt]
        exact (Int.le_ediv_iff_mul_le hs).symm
      have hdown : t.lo ≤ k * t.scale ↔ t.minInt ≤ k := by
        simp only [FxTy.minInt]
        have hx : -k ≤ (-t.lo) / t.scale ↔ -k * t.scale ≤ -t.lo := Int.le_ediv_iff_mul_le hs
        rw [Int.neg_mul] at hx
        constructor
        · intro h
          have h' : -k ≤ (-t.lo) / t.scale := hx.mpr (by omega)
          omega
        · intro h
          have h' : -(k * t.scale) ≤ -t.lo := hx.mp (by omega)
          omega
      simp only [FxTy.inRange]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · intro h; exact ⟨hdown.mp h.1, hup.mp h.2⟩
      · intro h; exact ⟨hdown.mpr h.1, hup.mpr h.2⟩
    · simp only [hi, if_false]

/-! ### The mobile type of a fractional constant -/

/-- solc's digit loop: multiply by `10` while the value stays at most
`maxV`, is not yet an integer and fewer than `80` digits are taken. -/
def digitsGo (a den maxV : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n =>
    if a * 10 ^ (n + 1) ≤ maxV * den ∧ a * 10 ^ n % den ≠ 0 then digitsGo a den maxV k (n + 1)
    else n

theorem digitsGo_le (a den maxV : Nat) : ∀ k n, digitsGo a den maxV k n ≤ n + k
  | 0, n => Nat.le_refl n
  | k + 1, n => by
    unfold digitsGo
    split
    · have h : digitsGo a den maxV k (n + 1) ≤ n + 1 + k := digitsGo_le a den maxV k (n + 1)
      omega
    · omega

/-- Bytes in the big-endian encoding of a number (solc's
`numberEncodingSize`), within `k` bytes. -/
def byteLen : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, v => if v = 0 then 0 else byteLen k (v / 256) + 1

theorem byteLen_spec : ∀ k v, v < 256 ^ k → v < 256 ^ byteLen k v ∧ byteLen k v ≤ k
  | 0, v, h => by
    simp only [Nat.pow_zero] at h
    simp only [byteLen, Nat.pow_zero, Nat.le_refl, and_true]
    exact h
  | k + 1, v, h => by
    unfold byteLen
    by_cases hv : v = 0
    · simp only [hv, if_true, Nat.pow_zero]
      omega
    · simp only [hv, if_false]
      have hp : 256 ^ (k + 1) = 256 ^ k * 256 := by rw [Nat.pow_succ]
      have hk : v / 256 < 256 ^ k := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        omega
      have ih : v / 256 < 256 ^ byteLen k (v / 256) ∧ byteLen k (v / 256) ≤ k :=
        byteLen_spec k (v / 256) hk
      have hp' : 256 ^ (byteLen k (v / 256) + 1) = 256 ^ byteLen k (v / 256) * 256 := by
        rw [Nat.pow_succ]
      refine ⟨?_, by omega⟩
      rw [hp']
      omega

/-- The bound of the magnitude: `2^255` for a negative constant, else
`2^256 - 1`. -/
def maxMag (q : Rat) : Nat := if q.num < 0 then 2 ^ 255 else 2 ^ 256 - 1

/-- The digits of the mobile type. -/
def mobDigits (q : Rat) : Nat := digitsGo q.num.natAbs q.den (maxMag q) 80 0

/-- The magnitude at those digits, truncated toward zero. -/
def mobMag (q : Rat) : Nat := q.num.natAbs * 10 ^ mobDigits q / q.den

/-- The number whose bytes give the width: the magnitude, or for a negative
constant `2·(magnitude − 1)` (one bit for the sign). -/
def mobWord (q : Rat) : Nat := if q.num < 0 ∧ mobMag q ≠ 0 then (mobMag q - 1) * 2 else mobMag q

/-- The width in bytes. -/
def mobBytes (q : Rat) : Nat := max (byteLen 32 (mobWord q)) 1

theorem mobDigits_le (q : Rat) : mobDigits q ≤ 80 := by
  have h : mobDigits q ≤ 0 + 80 := digitsGo_le _ _ _ 80 0
  omega

theorem mobBytes_le {q : Rat} (h : mobWord q < 256 ^ 32) : 1 ≤ mobBytes q ∧ mobBytes q ≤ 32 := by
  have hb : mobWord q < 256 ^ byteLen 32 (mobWord q) ∧ byteLen 32 (mobWord q) ≤ 32 :=
    byteLen_spec 32 _ h
  simp only [mobBytes]
  omega

/-- solc's mobile type of a fractional constant
(`RationalNumberType::fixedPointType`): as many digits as fit (at most 80),
truncated toward zero, in the fewest bytes, signed exactly when negative;
`none` (no type: a compile error where one is needed) when the magnitude
exceeds 256 bits. -/
def mobileFx? (q : Rat) : Option FxTy :=
  if q.num.natAbs * 10 ^ mobDigits q ≤ maxMag q * q.den then
    if hw : mobWord q < 256 ^ 32 then
      some ⟨decide (q.num < 0), 8 * mobBytes q, mobDigits q, by
        have hb : 1 ≤ mobBytes q ∧ mobBytes q ≤ 32 := mobBytes_le hw
        have hd : mobDigits q ≤ 80 := mobDigits_le q
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        omega⟩
    else none
  else none

theorem mobileFx?_spec {q : Rat} {t : FxTy} (h : mobileFx? q = some t) :
    t.signed = decide (q.num < 0) ∧ t.bits = 8 * mobBytes q ∧ t.digits = mobDigits q ∧
    mobWord q < 256 ^ 32 := by
  unfold mobileFx? at h
  split at h
  · split at h
    · rename_i hw
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, hw⟩
    · exact nomatch h
  · exact nomatch h

/-- The truncated scaled integer at the mobile type is the signed
magnitude. -/
theorem literalTrunc_mob {q : Rat} {t : FxTy} (h : t.digits = mobDigits q) :
    literalTrunc t q.num q.den = if q.num < 0 then -(mobMag q : Int) else (mobMag q : Int) := by
  have hpow : ((10 ^ mobDigits q : Nat) : Int) = (10 : Int) ^ mobDigits q := Int.natCast_pow 10 _
  have hsc : t.scale = ((10 ^ mobDigits q : Nat) : Int) := by
    simp only [FxTy.scale, h, hpow]
  have hm : (mobMag q : Int) = ((q.num.natAbs : Int) * (10 ^ mobDigits q : Nat)) / q.den := by
    simp only [mobMag, Int.natCast_ediv, Int.natCast_mul]
  unfold literalTrunc
  rw [hsc]
  by_cases hn : q.num < 0
  · have ha : q.num = -(q.num.natAbs : Int) := by omega
    simp only [hn, if_true]
    rw [ha, Int.neg_mul, Int.neg_tdiv, hm,
      Int.tdiv_eq_ediv_of_nonneg (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))]
  · have ha : q.num = (q.num.natAbs : Int) := by omega
    simp only [hn, if_false]
    rw [hm, ← ha, Int.tdiv_eq_ediv_of_nonneg (Int.mul_nonneg (by omega) (Int.natCast_nonneg _))]

/-- The mobile type holds the constant, truncated toward zero at its
digits. -/
theorem mobileFx?_inRange {q : Rat} {t : FxTy} (h : mobileFx? q = some t) :
    t.inRange (literalTrunc t q.num q.den) = true := by
  obtain ⟨hs, hb, hd, hw⟩ := mobileFx?_spec h
  rw [literalTrunc_mob hd]
  have hbl : mobWord q < 256 ^ byteLen 32 (mobWord q) ∧ byteLen 32 (mobWord q) ≤ 32 :=
    byteLen_spec 32 _ hw
  have hmono : 256 ^ byteLen 32 (mobWord q) ≤ 256 ^ mobBytes q :=
    Nat.pow_le_pow_right (by decide) (by simp only [mobBytes]; omega)
  have hpb : (2 : Nat) ^ t.bits = 256 ^ mobBytes q := by rw [hb, Nat.pow_mul]
  have hwl : mobWord q < 2 ^ t.bits := by omega
  have hcast : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := Int.natCast_pow 2 _
  have hp : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := t.pow_bits
  simp only [FxTy.inRange, FxTy.lo, FxTy.hi, hs, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hn : q.num < 0
  · simp only [hn, if_true]
    have hwq : mobWord q = if mobMag q ≠ 0 then (mobMag q - 1) * 2 else mobMag q := by
      simp only [mobWord, hn, true_and]
    have hh : (0 : Int) < 2 ^ (t.bits - 1) := t.half_pos
    by_cases hz : mobMag q = 0
    · simp only [hz, Int.natCast_zero, Int.neg_zero]
      omega
    · simp only [hz, ne_eq, not_false_eq_true, if_true] at hwq
      omega
  · simp only [hn, if_false]
    have hwq : mobWord q = mobMag q := by simp only [mobWord, hn, false_and, if_false]
    omega

/-- At its mobile type, a constant converts implicitly exactly when its
digits suffice. -/
theorem mobileFx?_exact {q : Rat} {t : FxTy} (h : mobileFx? q = some t) :
    (ofRat? t q).isSome = true ↔ (q.den : Int) ∣ q.num * t.scale := by
  constructor
  · intro hs
    cases ho : ofRat? t q with
    | none => rw [ho] at hs; exact nomatch hs
    | some a =>
      have he : a.1 * q.den = q.num * t.scale := ofRat?_eq_some_iff.mp ho
      exact ⟨a.1, by rw [← he, Int.mul_comm]⟩
  · intro hd
    have hr : t.inRange (literalTrunc t q.num q.den) = true := mobileFx?_inRange h
    have he : (⟨literalTrunc t q.num q.den, hr⟩ : Fx t).1 * q.den = q.num * t.scale := by
      simp only [literalTrunc]
      exact Int.tdiv_mul_cancel hd
    rw [(ofRat?_eq_some_iff).mpr he]
    rfl

/-- solc's digit loop stops at or before any digit count `d` at which the
constant is an integer and fits. -/
theorem digitsGo_le_of_exact (a den maxV d : Nat) (hd : a * 10 ^ d % den = 0) :
    ∀ k n, n ≤ d → digitsGo a den maxV k n ≤ d
  | 0, n, hn => hn
  | k + 1, n, hn => by
    unfold digitsGo
    split
    · rename_i hc
      have hne : n ≠ d := fun he => hc.2 (he ▸ hd)
      exact digitsGo_le_of_exact a den maxV d hd k (n + 1) (by omega)
    · exact hn

/-- …and the constant is exact where it stops. -/
theorem digitsGo_exact (a den maxV d : Nat) (hd : a * 10 ^ d % den = 0)
    (hm : a * 10 ^ d ≤ maxV * den) : ∀ k n, n ≤ d → d ≤ n + k →
      a * 10 ^ (digitsGo a den maxV k n) % den = 0
  | 0, n, hn, hk => by
    have he : n = d := by omega
    simp only [digitsGo, he]
    exact hd
  | k + 1, n, hn, hk => by
    unfold digitsGo
    split
    · rename_i hc
      have hne : n ≠ d := fun he => hc.2 (he ▸ hd)
      exact digitsGo_exact a den maxV d hd hm k (n + 1) (by omega) (by omega)
    · rename_i hc
      by_cases hz : a * 10 ^ n % den = 0
      · exact hz
      · -- the loop stopped on the magnitude, so `d` is `n`
        have hgt : ¬ a * 10 ^ (n + 1) ≤ maxV * den := fun hl => hc ⟨hl, hz⟩
        have hnd : ¬ n + 1 ≤ d := by
          intro hl
          have hp : 10 ^ (n + 1) ≤ 10 ^ d := Nat.pow_le_pow_right (by decide) hl
          have hmul : a * 10 ^ (n + 1) ≤ a * 10 ^ d := Nat.mul_le_mul_left a hp
          omega
        have he : n = d := by omega
        rw [he]
        exact hd

/-- The mobile type of a constant that is exact at some `d ≤ 80` digits
within the magnitude bound takes digits at which it is exact, so the
constant converts to it implicitly. -/
theorem mobileFx?_exact_of_digits {q : Rat} {t : FxTy} (h : mobileFx? q = some t) {d : Nat}
    (hd80 : d ≤ 80) (hd : q.num.natAbs * 10 ^ d % q.den = 0)
    (hm : q.num.natAbs * 10 ^ d ≤ maxMag q * q.den) : (ofRat? t q).isSome = true := by
  have hx : q.num.natAbs * 10 ^ (mobDigits q) % q.den = 0 :=
    digitsGo_exact _ _ _ d hd hm 80 0 (Nat.zero_le d) (by omega)
  have ht : t.digits = mobDigits q := (mobileFx?_spec h).2.2.1
  apply (mobileFx?_exact h).mpr
  have hn : (q.den : Int) ∣ (q.num.natAbs : Int) * ((10 ^ mobDigits q : Nat) : Int) := by
    have hdv : q.den ∣ q.num.natAbs * 10 ^ mobDigits q := Nat.dvd_of_mod_eq_zero hx
    exact Int.natCast_dvd_natCast.mpr hdv
  have hsc : t.scale = ((10 ^ mobDigits q : Nat) : Int) := by
    simp only [FxTy.scale, ht, Int.natCast_pow, Int.cast_ofNat_Int]
  rw [hsc]
  by_cases hneg : q.num < 0
  · have ha : q.num = -(q.num.natAbs : Int) := by omega
    rw [ha, Int.neg_mul]
    exact Int.dvd_neg.mpr hn
  · have ha : q.num = (q.num.natAbs : Int) := by omega
    rw [ha]
    exact hn

/-! ### solc's route through the mobile type -/

/-- The truncated constant at fewer digits is the truncated constant at
more digits, truncated again. -/
theorem literalTrunc_rescale {t t' : FxTy} (num : Int) {den : Nat} (hd : den ≠ 0)
    (h : t.digits ≤ t'.digits) :
    rescale t'.digits t.digits (literalTrunc t' num den) = literalTrunc t num den := by
  have hp : (0 : Int) < den := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hd)
  have hP : (0 : Int) < 10 ^ (t'.digits - t.digits) := Int.pow_pos (by decide)
  by_cases he : t'.digits ≤ t.digits
  · have hq : t.digits = t'.digits := Nat.le_antisymm h he
    have hs : t.scale = t'.scale := by simp only [FxTy.scale, hq]
    have hz : t.digits - t'.digits = 0 := by omega
    simp only [rescale, he, if_true, hz, Int.pow_zero, Int.mul_one, literalTrunc, hs]
  · simp only [rescale, he, if_false, literalTrunc]
    rw [tdiv_tdiv _ _ hp, ← Int.mul_tdiv_mul_of_pos_left (num * t.scale) (den : Int) hP]
    have hs : num * t.scale * 10 ^ (t'.digits - t.digits) = num * t'.scale := by
      simp only [FxTy.scale]
      rw [Int.mul_assoc, ← Int.pow_add, Nat.add_sub_cancel' h]
    rw [hs]

/-- When the target has no more digits than the mobile type, the route
through the mobile type — the constant typed there, then converted by this
model's run-time conversion (rescale toward zero, then wrap; Q2, Q3) — is
the wrap of the exactly folded value. -/
theorem explicit_mobile_route {q : Rat} {m t : FxTy} (hm : mobileFx? q = some m)
    (hd : t.digits ≤ m.digits) :
    explicit t (⟨literalTrunc m q.num q.den, mobileFx?_inRange hm⟩ : Fx m) =
      wrap t (literalTrunc t q.num q.den) := by
  have hr : rescale m.digits t.digits (literalTrunc m q.num q.den) = literalTrunc t q.num q.den :=
    literalTrunc_rescale q.num q.den_nz hd
  simp only [explicit, hr]

/-- …so where the exact fold fits the target (`explicitRat?` succeeds), the
route gives exactly the folded value: P1 changes no such conversion.  Out of
range, solc accepts and this model refuses (Q2). -/
theorem explicitRat?_mobile_route {q : Rat} {m t : FxTy} (hm : mobileFx? q = some m)
    (hd : t.digits ≤ m.digits) {a : Fx t} (ha : explicitRat? t q = some a) :
    explicit t (⟨literalTrunc m q.num q.den, mobileFx?_inRange hm⟩ : Fx m) = a := by
  have hv : a.1 = literalTrunc t q.num q.den := (explicitConst?_eq_some_iff q.den_nz).mp ha
  have hin : t.inRange (literalTrunc t q.num q.den) = true := by rw [← hv]; exact a.2
  rw [explicit_mobile_route hm hd]
  apply Subtype.ext
  simp only [wrap, wrapInt_of_inRange hin, hv]

/-! ### The common type with a constant operand -/

/-- The type `x op c` runs at, for `x : t` and a constant `c` (solc's
`Type::commonType(t, c)`): `t` if `c` converts to it implicitly; else, for a
fractional `c`, `c`'s mobile type if `t` converts to it (an integer
constant's mobile type is an integer type, to which no fixed-point type
converts) — and, as Q1 requires, only when `c` is exact there (solc would
truncate `c`, e.g. `ufixed8x77 x; x + 1/3` at `ufixed256x77`). -/
def litCommon? (t : FxTy) (q : Rat) : Option FxTy :=
  if (Fx.ofRat? t q).isSome then some t
  else if q.den = 1 then none
  else match mobileFx? q with
    | some m => if t.implicitOK m && (Fx.ofRat? m q).isSome then some m else none
    | none => none

/-- `c op x`, as solc's `RationalNumberType::binaryOperatorResult`: a
fractional `c` is refused ("Fractional literals not supported."); an
integer `c` runs at `t` when it converts implicitly. -/
def litCommonRev? (q : Rat) (t : FxTy) : Option FxTy :=
  if q.den = 1 ∧ (Fx.ofRat? t q).isSome = true then some t else none

/-- solc's `Type::commonType(t, c)` for a fixed-point `t` and a constant
`c`, transcribed (`Types.cpp:286–296`, the mobile types from
`Types.cpp:1207–1213`). -/
def solcLitCommon (t : FxTy) (q : Rat) : Option FxTy :=
  if solcLiteralOK t q.num q.den then some t
  else if q.den = 1 then none
  else match mobileFx? q with
    | some m => if t.solcImplicit m then some m else none
    | none => none

/-- solc's `c op x` for a fixed-point `x : t`, transcribed
(`Types.cpp:1075–1078` and the common type). -/
def solcLitCommonRev (q : Rat) (t : FxTy) : Option FxTy :=
  if q.den = 1 ∧ solcLiteralOK t q.num q.den = true then some t else none

/-- `x op c` is typed only where solc types it, at the same type. -/
theorem litCommon?_solc {t u : FxTy} {q : Rat} (h : litCommon? t q = some u) :
    solcLitCommon t q = some u := by
  have hs : (ofRat? t q).isSome = solcLiteralOK t q.num q.den :=
    ofLiteral?_isSome_iff_solc q.den_nz
  unfold litCommon? at h
  unfold solcLitCommon
  rw [← hs]
  by_cases h1 : (Fx.ofRat? t q).isSome = true
  · simp only [h1, if_true] at h ⊢
    exact h
  · simp only [h1, Bool.false_eq_true, if_false] at h ⊢
    by_cases h0 : q.den = 1
    · simp only [h0, if_true] at h
      exact nomatch h
    · simp only [h0, if_false] at h ⊢
      split at h
      · rename_i m _
        by_cases h2 : (t.implicitOK m && (Fx.ofRat? m q).isSome) = true
        · simp only [h2, if_true] at h
          simp only [Bool.and_eq_true, FxTy.implicitOK] at h2
          simp only [h2.1.1, if_true]
          exact h
        · simp only [h2, Bool.false_eq_true, if_false] at h
          exact nomatch h
      · exact nomatch h

/-- `c op x` is exactly solc's. -/
theorem litCommonRev?_eq_solc (q : Rat) (t : FxTy) : litCommonRev? q t = solcLitCommonRev q t := by
  have hs : (ofRat? t q).isSome = solcLiteralOK t q.num q.den :=
    ofLiteral?_isSome_iff_solc q.den_nz
  simp only [litCommonRev?, solcLitCommonRev, hs]

/-- At a common type with a constant, both operands are exact. -/
theorem litCommon?_exact {t u : FxTy} {q : Rat} (h : litCommon? t q = some u) :
    t.subsumes u = true ∧ (Fx.ofRat? u q).isSome = true := by
  unfold litCommon? at h
  by_cases h1 : (Fx.ofRat? t q).isSome = true
  · simp only [h1, if_true, Option.some.injEq] at h
    subst h
    exact ⟨FxTy.subsumes_refl t, h1⟩
  · simp only [h1, Bool.false_eq_true, if_false] at h
    by_cases h0 : q.den = 1
    · simp only [h0, if_true] at h
      exact nomatch h
    · simp only [h0, if_false] at h
      split at h
      · rename_i m _
        by_cases h2 : (t.implicitOK m && (Fx.ofRat? m q).isSome) = true
        · simp only [h2, if_true, Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at h2
          exact ⟨FxTy.implicitOK_iff.mp h2.1, h2.2⟩
        · simp only [h2, Bool.false_eq_true, if_false] at h
          exact nomatch h
      · exact nomatch h

theorem litCommonRev?_exact {t u : FxTy} {q : Rat} (h : litCommonRev? q t = some u) :
    u = t ∧ (Fx.ofRat? u q).isSome = true := by
  unfold litCommonRev? at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, hc.2⟩
  · exact nomatch h

end Fx

/-! ### Worked values -/

section Examples

open Fx

/-- `0.1 + 0.2 == 0.3` exactly, and `(1 / 3) * 3 == 1`: folding keeps no
intermediate rounding. -/
example : CExpr.eval (.add (.lit (mkRat 1 10)) (.lit (mkRat 2 10))) = some (mkRat 3 10) ∧
    CExpr.eval (.mul (.div (.lit 1) (.lit 3)) (.lit 3)) = some 1 := by
  decide +kernel

/-- `1 / 0` and `1 % 0` are compile errors; `2 ** -2 == 0.25`; `2 ** 0.5`
is refused (a fractional exponent); `-7.5 % 2 == -1.5` (the sign of the
dividend). -/
example : CExpr.eval (.div (.lit 1) (.lit 0)) = none ∧
    CExpr.eval (.mod (.lit 1) (.lit 0)) = none ∧
    CExpr.eval (.pow (.lit 2) (.lit (-2))) = some (mkRat 1 4) ∧
    CExpr.eval (.pow (.lit 2) (.lit (mkRat 1 2))) = none ∧
    CExpr.eval (.mod (.lit (mkRat (-15) 2)) (.lit 2)) = some (mkRat (-3) 2) := by
  decide +kernel

/-- solc's precision pre-check for powers: `2 ** 2048` folds; `2 ** 2049`
is refused, since `2049 · (1 + 1) > 4096` bits may be needed. -/
example : (CExpr.eval (.pow (.lit 2) (.lit 2048))).isSome ∧
    CExpr.eval (.pow (.lit 2) (.lit 2049)) = none := by
  decide +kernel

/-- Mobile types: `0.5` is `ufixed8x1`, `-12.8` is `fixed8x1`, `-12.9` is
`fixed16x1`, `1/3` is `ufixed256x77` (as many digits as fit) and
`2^256 + 0.5` has none. -/
example : (mobileFx? (mkRat 1 2)).map (fun t => (t.signed, t.bits, t.digits)) =
      some (false, 8, 1) ∧
    (mobileFx? (mkRat (-128) 10)).map (fun t => (t.signed, t.bits, t.digits)) =
      some (true, 8, 1) ∧
    (mobileFx? (mkRat (-129) 10)).map (fun t => (t.signed, t.bits, t.digits)) =
      some (true, 16, 1) ∧
    (mobileFx? (mkRat 1 3)).map (fun t => (t.signed, t.bits, t.digits)) =
      some (false, 256, 77) ∧
    (mobileFx? (mkRat (2 ^ 257 + 1) 2)).isSome = false := by
  decide +kernel

/-- An explicit conversion of an out-of-range constant is a compile error
(Q2): `ufixed256x80(1/3)` needs `3.3·10^79 > 2^256`, where solc's type
checker admits it through the mobile type; `ufixed256x77(1/3)` holds 77
threes. -/
example : (explicitRat? ⟨false, 256, 80, by decide⟩ (mkRat 1 3)).isNone ∧
    (explicitRat? ⟨false, 256, 77, by decide⟩ (mkRat 1 3)).map Subtype.val =
      some ((10 ^ 77 - 1) / 3) := by
  decide +kernel

/-- Exact folding at the target's digits (P1) differs from solc's route
through the mobile type: `c = (2^257 - 1) / 20` has mobile type
`ufixed256x0` (`10·c` exceeds `2^256 - 1`), so solc would convert
`ufixed256x1(c)` from `trunc(c)`, giving `2^256 - 6`; folded exactly it is
`trunc(10·c) = 2^256 - 1`. -/
example : (mobileFx? (mkRat (2 ^ 257 - 1) 20)).map (fun t => (t.signed, t.bits, t.digits)) =
      some (false, 256, 0) ∧
    (explicitRat? ⟨false, 256, 1, by decide⟩ (mkRat (2 ^ 257 - 1) 20)).map Subtype.val =
      some (2 ^ 256 - 1) ∧
    ((2 ^ 257 - 1) / 20 : Int) * 10 = 2 ^ 256 - 6 := by
  decide +kernel

/-- `ufixed8x1 x; x + 0.5` runs at `ufixed8x1`; `x + 0.25` is refused (no
exact type for both); `ufixed8x77 y; y + 1/3` is refused, where solc
would truncate the constant at `ufixed256x77`; `ufixed8x0 z; z + 300` is
refused as in solc (the mobile type of `300` is `uint16`); `0.5 + x` is
refused as in solc; `2 + x` runs at `ufixed8x1`. -/
example : (litCommon? ⟨false, 8, 1, by decide⟩ (mkRat 1 2)).map (·.digits) = some 1 ∧
    litCommon? ⟨false, 8, 1, by decide⟩ (mkRat 1 4) = none ∧
    litCommon? ⟨false, 8, 77, by decide⟩ (mkRat 1 3) = none ∧
    (solcLitCommon ⟨false, 8, 77, by decide⟩ (mkRat 1 3)).map (·.bits) = some 256 ∧
    litCommon? ⟨false, 8, 0, by decide⟩ 300 = none ∧
    litCommonRev? (mkRat 1 2) ⟨false, 8, 1, by decide⟩ = none ∧
    (litCommonRev? 2 ⟨false, 8, 1, by decide⟩).map (·.digits) = some 1 := by
  decide +kernel

/-- A constant just below `2^256` has no mobile type (`10^0 · c` exceeds
`2^256 - 1`), so solc refuses `ufixed256x0(c)` for `c = 2^256 - 1/2`; folded
exactly it is `2^256 - 1`. -/
example : (mobileFx? (mkRat (2 ^ 257 - 1) 2)).isSome = false ∧
    (explicitRat? ⟨false, 256, 0, by decide⟩ (mkRat (2 ^ 257 - 1) 2)).map Subtype.val =
      some (2 ^ 256 - 1) := by
  decide +kernel

end Examples

/-! ### Axiom pins -/

/--
info: 'Solidity.Language.FixedPoint.Fx.ofLiteral?_isSome_iff_solc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.ofLiteral?_isSome_iff_solc

/--
info: 'Solidity.Language.FixedPoint.Fx.explicitConst?_eq_none_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fx.explicitConst?_eq_none_iff

/--
info: 'Solidity.Language.FixedPoint.Fx.mobileFx?_inRange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.mobileFx?_inRange

/--
info: 'Solidity.Language.FixedPoint.Fx.litCommon?_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.litCommon?_exact

/--
info: 'Solidity.Language.FixedPoint.Fx.litCommon?_solc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.litCommon?_solc

/--
info: 'Solidity.Language.FixedPoint.Fx.explicitRat?_mobile_route' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.explicitRat?_mobile_route

/--
info: 'Solidity.Language.FixedPoint.Fx.mobileFx?_exact_of_digits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.mobileFx?_exact_of_digits

end Solidity.Language.FixedPoint
