import Solidity.Language.FixedPoint

/-!
# Fixed-point laws

The laws of `Solidity/Language/FixedPoint.lean` the reviews of the
second-round decisions asked for (`docs/feature-work/fixed-point-semantics.md`,
§6.1): checked and unchecked arithmetic agree wherever nothing overflows;
`*` and `/` are exact when the exact result has at most `N` digits and
otherwise truncate toward zero by less than one unit in the last place, as
the digit-dropping conversions do; lossless conversions round-trip; the
implicit conversion is exactly the range-contained one
(`FxTy.implicitOK_iff`, `FxTy.subsumes_iff`) and keeps the value and the
order.

A checked `*` or `/` range-checks the truncated exact result only: the
exact product or quotient is an unbounded intermediate (Q8), so no
overflow of a 512-bit or 256-bit intermediate is observable.
-/

namespace Solidity.Language.FixedPoint

/-! ### Truncating division -/

/-- `tdiv` by a positive divisor truncates toward zero: `q·d` lies between
`0` and `x`, less than one `d` away from `x`. -/
theorem tdiv_trunc (x d : Int) (hd : 0 < d) :
    (0 ≤ x → 0 ≤ x.tdiv d * d ∧ x.tdiv d * d ≤ x ∧ x < x.tdiv d * d + d) ∧
    (x < 0 → x.tdiv d * d - d < x ∧ x ≤ x.tdiv d * d ∧ x.tdiv d * d ≤ 0) := by
  have he : x.tmod d + x.tdiv d * d = x := Int.tmod_add_tdiv_mul x d
  have h1 : x.tmod d < d := Int.tmod_lt_of_pos x hd
  have h2 : -d < x.tmod d := Int.lt_tmod_of_pos x hd
  have hb : (0 ≤ x → 0 ≤ x.tmod d ∧ x.tmod d ≤ x) ∧ (x < 0 → x ≤ x.tmod d ∧ x.tmod d ≤ 0) :=
    Fx.tmod_between x d
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hm : 0 ≤ x.tmod d ∧ x.tmod d ≤ x := hb.1 hx
    omega
  · have hm : x ≤ x.tmod d ∧ x.tmod d ≤ 0 := hb.2 hx
    omega

/-- The remainder of a truncating division by any nonzero `b` has the sign
of the dividend and is smaller than `b` in magnitude. -/
theorem tdiv_rem (x b : Int) (hb : b ≠ 0) :
    x = x.tdiv b * b + x.tmod b ∧ (x.tmod b).natAbs < b.natAbs ∧
    (0 ≤ x → 0 ≤ x.tmod b) ∧ (x < 0 → x.tmod b ≤ 0) := by
  have he : x.tmod b + x.tdiv b * b = x := Int.tmod_add_tdiv_mul x b
  have hn : (x.tmod b).natAbs = x.natAbs % b.natAbs := Int.natAbs_tmod x b
  have hpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hlt : x.natAbs % b.natAbs < b.natAbs := Nat.mod_lt _ hpos
  have hs : (0 ≤ x → 0 ≤ x.tmod b ∧ x.tmod b ≤ x) ∧ (x < 0 → x ≤ x.tmod b ∧ x.tmod b ≤ 0) :=
    Fx.tmod_between x b
  refine ⟨by omega, by omega, fun hx => (hs.1 hx).1, fun hx => (hs.2 hx).2⟩

theorem pow_two_le {m n : Nat} (h : (2 : Int) ^ m ≤ 2 ^ n) : m ≤ n := by
  have e1 : ((2 ^ m : Nat) : Int) = (2 : Int) ^ m := Int.natCast_pow 2 m
  have e2 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := Int.natCast_pow 2 n
  have hn : 2 ^ m ≤ 2 ^ n := by omega
  exact (Nat.pow_le_pow_iff_right (by decide)).mp hn

theorem pow_ten_ne (n : Nat) : (10 : Int) ^ n ≠ 0 := by
  have h : (0 : Int) < 10 ^ n := Int.pow_pos (by decide)
  omega

/-- Truncations compose: truncating by `a`, then by `b`, is truncating by
`a·b`. -/
theorem tdiv_tdiv (x : Int) {a : Int} (b : Int) (ha : 0 < a) :
    (x.tdiv a).tdiv b = x.tdiv (a * b) := by
  have hab : 0 ≤ a := Int.le_of_lt ha
  by_cases hx : 0 ≤ x
  · have h1 : 0 ≤ x / a := Int.ediv_nonneg hx hab
    rw [Int.tdiv_eq_ediv_of_nonneg hx, Int.tdiv_eq_ediv_of_nonneg h1,
      Int.tdiv_eq_ediv_of_nonneg hx, Int.ediv_ediv hab]
  · have hx' : 0 ≤ -x := by omega
    have h1 : 0 ≤ (-x) / a := Int.ediv_nonneg hx' hab
    have e1 : x.tdiv a = -((-x) / a) := by
      rw [← Int.neg_neg x, Int.neg_tdiv, Int.neg_neg, Int.tdiv_eq_ediv_of_nonneg hx']
    have e2 : x.tdiv (a * b) = -((-x) / (a * b)) := by
      rw [← Int.neg_neg x, Int.neg_tdiv, Int.neg_neg, Int.tdiv_eq_ediv_of_nonneg hx']
    rw [e1, e2, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg h1, Int.ediv_ediv hab]

namespace Fx

variable {t t' : FxTy}

/-! ### Checked and unchecked agree where nothing overflows -/

/-- Where a checked result exists, the unchecked one is the same value. -/
theorem result_unchecked_of_checked {v : Int} {r : Fx t}
    (h : result .checked t v = .ok r) : result .unchecked t v = .ok r := by
  by_cases hv : t.inRange v = true
  · rw [result_of_inRange .checked hv] at h
    rw [result_of_inRange .unchecked hv, h]
  · simp only [result, hv, Bool.false_eq_true, dite_false] at h
    exact nomatch h

/-- In range, both modes give the same result. -/
theorem result_agree {v : Int} (h : t.inRange v = true) :
    result .checked t v = result .unchecked t v := by
  rw [result_of_inRange .checked h, result_of_inRange .unchecked h]

/-! Where the exact result does not overflow, the two modes agree. -/

theorem add_agree_of_inRange {a b : Fx t} (h : t.inRange (a.1 + b.1) = true) :
    add .checked a b = add .unchecked a b := result_agree h

theorem sub_agree_of_inRange {a b : Fx t} (h : t.inRange (a.1 - b.1) = true) :
    sub .checked a b = sub .unchecked a b := result_agree h

theorem neg_agree_of_inRange {a : Fx t} (h : t.inRange (-a.1) = true) :
    neg .checked a = neg .unchecked a := result_agree h

theorem mul_agree_of_inRange {a b : Fx t} (h : t.inRange ((a.1 * b.1).tdiv t.scale) = true) :
    mul .checked a b = mul .unchecked a b := result_agree h

theorem inc_agree_of_inRange {a : Fx t} (h : t.inRange (a.1 + t.scale) = true) :
    inc .checked a = inc .unchecked a := result_agree h

theorem dec_agree_of_inRange {a : Fx t} (h : t.inRange (a.1 - t.scale) = true) :
    dec .checked a = dec .unchecked a := result_agree h

/-- Division agrees where its exact quotient does not overflow; a zero
divisor panics in both modes. -/
theorem div_agree_of_inRange {a b : Fx t}
    (h : b.1 ≠ 0 → t.inRange ((a.1 * t.scale).tdiv b.1) = true) :
    div .checked a b = div .unchecked a b := by
  by_cases hb : b.1 = 0
  · simp only [div, hb, if_true]
  · simp only [div, hb, if_false]
    exact result_agree (h hb)

/-- `%` never overflows, so the two modes always agree. -/
theorem mod_agree' (a b : Fx t) : mod .checked a b = mod .unchecked a b := by
  by_cases hb : b.1 = 0
  · simp only [mod, hb, if_true]
  · simp only [mod, hb, if_false]
    exact result_agree (mod_inRange a b)

/-! The same agreement read from a checked success. -/

theorem add_agree {a b : Fx t} {r : Fx t} (h : add .checked a b = .ok r) :
    add .unchecked a b = .ok r := result_unchecked_of_checked h

theorem sub_agree {a b : Fx t} {r : Fx t} (h : sub .checked a b = .ok r) :
    sub .unchecked a b = .ok r := result_unchecked_of_checked h

theorem neg_agree {a : Fx t} {r : Fx t} (h : neg .checked a = .ok r) :
    neg .unchecked a = .ok r := result_unchecked_of_checked h

theorem mul_agree {a b : Fx t} {r : Fx t} (h : mul .checked a b = .ok r) :
    mul .unchecked a b = .ok r := result_unchecked_of_checked h

theorem inc_agree {a : Fx t} {r : Fx t} (h : inc .checked a = .ok r) :
    inc .unchecked a = .ok r := result_unchecked_of_checked h

theorem dec_agree {a : Fx t} {r : Fx t} (h : dec .checked a = .ok r) :
    dec .unchecked a = .ok r := result_unchecked_of_checked h

theorem div_agree {a b : Fx t} {r : Fx t} (h : div .checked a b = .ok r) :
    div .unchecked a b = .ok r := by
  rw [← div_agree_of_inRange (a := a) (b := b) ?_]
  · exact h
  · intro hb
    simp only [div, hb, if_false] at h
    by_cases hv : t.inRange ((a.1 * t.scale).tdiv b.1) = true
    · exact hv
    · simp only [result, hv, Bool.false_eq_true, dite_false] at h
      exact nomatch h

theorem mod_agree {a b : Fx t} {r : Fx t} (h : mod .checked a b = .ok r) :
    mod .unchecked a b = .ok r := by
  rw [← mod_agree' a b]
  exact h

/-- Every result of an operation is the wrapped exact scaled integer:
the unchecked result always, the checked one whenever it exists. -/
theorem result_val {m : Mode} {v : Int} {r : Fx t} (h : result m t v = .ok r) :
    r.1 = wrapInt t v := by
  cases m
  · by_cases hv : t.inRange v = true
    · rw [result_of_inRange .checked hv] at h
      cases h
      exact (wrapInt_of_inRange hv).symm
    · simp only [result, hv, Bool.false_eq_true, dite_false] at h
      exact nomatch h
  · simp only [result] at h
    cases h
    rfl

/-- A checked result is the exact scaled integer itself. -/
theorem result_checked_val {v : Int} {r : Fx t} (h : result .checked t v = .ok r) :
    r.1 = v := by
  by_cases hv : t.inRange v = true
  · rw [result_of_inRange .checked hv] at h
    cases h
    rfl
  · simp only [result, hv, Bool.false_eq_true, dite_false] at h
    exact nomatch h

/-- Unary minus at a `ufixed` type (Q5): checked, `0x11` unless the operand
is `0`; unchecked it wraps (`neg_agree`, `result_val`). -/
theorem neg_unsigned (hs : t.signed = false) (a : Fx t) :
    neg .checked a = if a.1 = 0 then .ok a else .error .overflow := by
  have ha : t.inRange a.1 = true := a.2
  simp only [FxTy.inRange, FxTy.lo, hs, Bool.false_eq_true, if_false, Bool.and_eq_true,
    decide_eq_true_eq] at ha
  by_cases h0 : a.1 = 0
  · have hv : t.inRange (-a.1) = true := by rw [h0, Int.neg_zero, ← h0]; exact a.2
    rw [if_pos h0]
    show result .checked t (-a.1) = .ok a
    rw [result_of_inRange .checked hv]
    exact congrArg Except.ok (Subtype.ext (by simp only [h0, Int.neg_zero]))
  · have hv : t.inRange (-a.1) = false := by
      simp only [FxTy.inRange, FxTy.lo, hs, Bool.false_eq_true, if_false, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      omega
    simp only [h0, if_false, neg]
    exact result_checked_overflow hv

/-! ### `*` and `/`: exact, then truncated toward zero -/

/-- A checked product is the exact product truncated toward zero: `r·10^N`
lies between `0` and `a·b`, less than one `10^N` away (an error below one
unit in the last place, Q3, Q8).  An unchecked product is the wrap of the
same integer (`mul_agree`, `result_val`). -/
theorem mul_trunc {a b r : Fx t} (h : mul .checked a b = .ok r) :
    (0 ≤ a.1 * b.1 → 0 ≤ r.1 * t.scale ∧ r.1 * t.scale ≤ a.1 * b.1 ∧
      a.1 * b.1 < r.1 * t.scale + t.scale) ∧
    (a.1 * b.1 < 0 → r.1 * t.scale - t.scale < a.1 * b.1 ∧ a.1 * b.1 ≤ r.1 * t.scale ∧
      r.1 * t.scale ≤ 0) := by
  have hr : r.1 = (a.1 * b.1).tdiv t.scale := result_checked_val h
  rw [hr]
  exact tdiv_trunc _ _ t.scale_pos

/-- A checked product whose exact value has at most `N` digits is exact. -/
theorem mul_exact {a b r : Fx t} (h : mul .checked a b = .ok r)
    (hd : t.scale ∣ a.1 * b.1) : r.1 * t.scale = a.1 * b.1 := by
  have hr : r.1 = (a.1 * b.1).tdiv t.scale := result_checked_val h
  rw [hr]
  exact Int.tdiv_mul_cancel hd

/-- A checked quotient is the exact quotient truncated toward zero:
`a·10^N = r·b + e` with `|e| < |b|` and `e` of the sign of `a` (Q3, Q8),
which determines `r`. -/
theorem div_trunc {a b r : Fx t} (h : div .checked a b = .ok r) :
    b.1 ≠ 0 ∧ ∃ e : Int, a.1 * t.scale = r.1 * b.1 + e ∧ e.natAbs < b.1.natAbs ∧
      (0 ≤ a.1 → 0 ≤ e) ∧ (a.1 < 0 → e ≤ 0) := by
  by_cases hb : b.1 = 0
  · simp only [div, hb, if_true] at h
    exact nomatch h
  · simp only [div, hb, if_false] at h
    have hr : r.1 = (a.1 * t.scale).tdiv b.1 := result_checked_val h
    have hs : 0 < t.scale := t.scale_pos
    have hq : a.1 * t.scale = (a.1 * t.scale).tdiv b.1 * b.1 + (a.1 * t.scale).tmod b.1 ∧
        ((a.1 * t.scale).tmod b.1).natAbs < b.1.natAbs ∧
        (0 ≤ a.1 * t.scale → 0 ≤ (a.1 * t.scale).tmod b.1) ∧
        (a.1 * t.scale < 0 → (a.1 * t.scale).tmod b.1 ≤ 0) :=
      tdiv_rem (a.1 * t.scale) b.1 hb
    refine ⟨hb, (a.1 * t.scale).tmod b.1, ?_, hq.2.1, fun ha => ?_, fun ha => ?_⟩
    · rw [hr]; exact hq.1
    · exact hq.2.2.1 (Int.mul_nonneg ha (by omega))
    · exact hq.2.2.2 (Int.mul_neg_of_neg_of_pos ha hs)

/-- A checked quotient whose exact value has at most `N` digits is exact. -/
theorem div_exact {a b r : Fx t} (h : div .checked a b = .ok r)
    (hd : b.1 ∣ a.1 * t.scale) : r.1 * b.1 = a.1 * t.scale := by
  by_cases hb : b.1 = 0
  · simp only [div, hb, if_true] at h
    exact nomatch h
  · simp only [div, hb, if_false] at h
    have hr : r.1 = (a.1 * t.scale).tdiv b.1 := result_checked_val h
    rw [hr]
    exact Int.tdiv_mul_cancel hd

/-- Checked `++` and `--` move the value by exactly `1` (Q6); unchecked they
wrap the same integer (`result_val`). -/
theorem inc_val {a r : Fx t} (h : inc .checked a = .ok r) : r.1 = a.1 + t.scale :=
  result_checked_val h

theorem dec_val {a r : Fx t} (h : dec .checked a = .ok r) : r.1 = a.1 - t.scale :=
  result_checked_val h

/-! ### Conversions: truncation and lossless round trips -/

/-- Dropping digits truncates toward zero: the rescaled integer, scaled
back, lies between `0` and `v`, less than one dropped unit away (Q3). -/
theorem rescale_down_trunc (n n' : Nat) (h : n' < n) (v : Int) :
    (0 ≤ v → 0 ≤ rescale n n' v * 10 ^ (n - n') ∧ rescale n n' v * 10 ^ (n - n') ≤ v ∧
      v < rescale n n' v * 10 ^ (n - n') + 10 ^ (n - n')) ∧
    (v < 0 → rescale n n' v * 10 ^ (n - n') - 10 ^ (n - n') < v ∧
      v ≤ rescale n n' v * 10 ^ (n - n') ∧ rescale n n' v * 10 ^ (n - n') ≤ 0) := by
  have hn : ¬ n ≤ n' := Nat.not_le.mpr h
  simp only [rescale, hn, if_false]
  exact tdiv_trunc v _ (Int.pow_pos (by decide))

/-- Dropping digits that are zero is exact: rescaling back gives `v`. -/
theorem rescale_down_exact (n n' : Nat) (v : Int) (hd : n' < n → 10 ^ (n - n') ∣ v) :
    rescale n' n (rescale n n' v) = v := by
  by_cases hle : n ≤ n'
  · by_cases he : n' ≤ n
    · have hnn : n = n' := Nat.le_antisymm hle he
      subst hnn
      simp only [rescale, Nat.le_refl, if_true, Nat.sub_self, Int.pow_zero, Int.mul_one]
    · simp only [rescale, hle, if_true, he, if_false]
      exact Int.mul_tdiv_cancel v (pow_ten_ne _)
  · have hlt : n' < n := Nat.lt_of_not_le hle
    have hle' : n' ≤ n := Nat.le_of_lt hlt
    simp only [rescale, hle, if_false, hle', if_true]
    exact Int.tdiv_mul_cancel (hd hlt)

/-- Dropping digits in two steps is dropping them at once. -/
theorem rescale_rescale_down (n m k : Nat) (h1 : k ≤ m) (h2 : m ≤ n) (v : Int) :
    rescale m k (rescale n m v) = rescale n k v := by
  have hp : ∀ e : Nat, (0 : Int) < 10 ^ e := fun e => Int.pow_pos (by decide)
  by_cases hmn : n ≤ m
  · have he : n = m := Nat.le_antisymm hmn h2
    subst he
    simp only [rescale, Nat.le_refl, if_true, Nat.sub_self, Int.pow_zero, Int.mul_one]
  · by_cases hkm : m ≤ k
    · have he : k = m := Nat.le_antisymm h1 hkm
      subst he
      simp only [rescale, Nat.le_refl, if_true, Nat.sub_self, Int.pow_zero, Int.mul_one]
    · have hnk : ¬ n ≤ k := by omega
      simp only [rescale, hmn, hkm, hnk, if_false]
      rw [tdiv_tdiv v _ (hp _), ← Int.pow_add]
      have he : n - m + (m - k) = n - k := by omega
      rw [he]

/-- Rescaling is monotone. -/
theorem rescale_mono (n n' : Nat) {v w : Int} (h : v ≤ w) : rescale n n' v ≤ rescale n n' w := by
  have hp : ∀ e : Nat, (0 : Int) < 10 ^ e := fun e => Int.pow_pos (by decide)
  unfold rescale
  split
  · exact Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt (hp _))
  · exact Int.tdiv_le_tdiv (hp _) h

/-- Rescaling up and back down is the identity. -/
theorem rescale_up_down (n n' : Nat) (h : n ≤ n') (v : Int) :
    rescale n' n (rescale n n' v) = v :=
  rescale_down_exact n n' v (fun hlt => absurd h (Nat.not_le.mpr hlt))

/-- An explicit conversion is value-preserving whenever the value is
representable at the target: no nonzero digit dropped and the rescaled
integer in range.  This covers a narrower width, the other signedness and
fewer digits, value by value. -/
theorem explicit_sameValue (a : Fx t)
    (hd : t'.digits < t.digits → 10 ^ (t.digits - t'.digits) ∣ a.1)
    (hr : t'.inRange (rescale t.digits t'.digits a.1) = true) :
    SameValue a (explicit t' a) := by
  simp only [SameValue, explicit, wrap, wrapInt_of_inRange hr, FxTy.scale]
  by_cases hle : t.digits ≤ t'.digits
  · simp only [rescale, hle, if_true]
    have hp : (10 : Int) ^ t'.digits = 10 ^ (t'.digits - t.digits) * 10 ^ t.digits := by
      rw [← Int.pow_add, Nat.sub_add_cancel hle]
    rw [hp, Int.mul_assoc]
  · have hlt : t'.digits < t.digits := Nat.lt_of_not_le hle
    simp only [rescale, hle, if_false]
    have hp : (10 : Int) ^ t.digits = 10 ^ (t.digits - t'.digits) * 10 ^ t'.digits := by
      rw [← Int.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
    have hc : a.1.tdiv (10 ^ (t.digits - t'.digits)) * 10 ^ (t.digits - t'.digits) = a.1 :=
      Int.tdiv_mul_cancel (hd hlt)
    rw [hp, ← Int.mul_assoc, hc]

/-- Under the same premises the explicit conversion back gives the value
back. -/
theorem explicit_explicit (a : Fx t)
    (hd : t'.digits < t.digits → 10 ^ (t.digits - t'.digits) ∣ a.1)
    (hr : t'.inRange (rescale t.digits t'.digits a.1) = true) :
    explicit t (explicit t' a) = a := by
  apply Subtype.ext
  simp only [explicit, wrap, wrapInt_of_inRange hr, rescale_down_exact _ _ _ hd,
    wrapInt_of_inRange a.2]

/-- An implicit conversion followed by the explicit conversion back gives
the value back. -/
theorem explicit_implicit (h : t.subsumes t' = true) (a : Fx t) :
    explicit t (implicit h a) = a := by
  rw [← explicit_of_subsumes h a]
  have hd : t.digits ≤ t'.digits := by
    simp only [FxTy.subsumes, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hr : t'.inRange (rescale t.digits t'.digits a.1) = true := by
    simp only [rescale, hd, if_true]
    exact inRange_mul_of_subsumes h a
  exact explicit_explicit a (fun hlt => absurd hd (Nat.not_le.mpr hlt)) hr

/-- An integer converted explicitly and converted back gives the integer
back, when its scaled value is in range. -/
theorem toIntTrunc_ofIntegerExplicit (k : Int) (h : t.inRange (k * t.scale) = true) :
    toIntTrunc (ofIntegerExplicit t k) = k := by
  have hs : 0 < t.scale := t.scale_pos
  simp only [toIntTrunc, ofIntegerExplicit, wrap, wrapInt_of_inRange h]
  exact Int.mul_tdiv_cancel k (by omega)

/-- A value with no fractional part converted to an integer and back is the
value. -/
theorem ofIntegerExplicit_toIntTrunc (a : Fx t) (h : t.scale ∣ a.1) :
    ofIntegerExplicit t (toIntTrunc a) = a := by
  apply Subtype.ext
  simp only [ofIntegerExplicit, toIntTrunc, wrap, Int.tdiv_mul_cancel h, wrapInt_of_inRange a.2]

/-- Conversion to an integer truncates toward zero (Q3, Q7). -/
theorem toIntTrunc_trunc (a : Fx t) :
    (0 ≤ a.1 → 0 ≤ toIntTrunc a * t.scale ∧ toIntTrunc a * t.scale ≤ a.1 ∧
      a.1 < toIntTrunc a * t.scale + t.scale) ∧
    (a.1 < 0 → toIntTrunc a * t.scale - t.scale < a.1 ∧ a.1 ≤ toIntTrunc a * t.scale ∧
      toIntTrunc a * t.scale ≤ 0) :=
  tdiv_trunc a.1 t.scale t.scale_pos

/-- A bit pattern read as a value and back is the bit pattern (`bytesM`
by bit pattern, Q7). -/
theorem toBits_ofBits {u : Int} (h0 : 0 ≤ u) (h1 : u < 2 ^ t.bits) :
    toBits (ofBits t u) = u := by
  simp only [toBits, ofBits, wrap, wrapInt_emod]
  exact Int.emod_eq_of_lt h0 h1

/-- A value's bit pattern read back is the value. -/
theorem ofBits_toBits (a : Fx t) : ofBits t (toBits a) = a := by
  apply Subtype.ext
  have he : wrapInt t (a.1 % 2 ^ t.bits) = wrapInt t a.1 := by
    unfold wrapInt
    simp only [Int.emod_emod]
  simp only [ofBits, toBits, wrap, he, wrapInt_of_inRange a.2]

/-- An explicit conversion keeps the order of the values it does not
wrap. -/
theorem explicit_le {a b : Fx t} (h : le a b = true)
    (ha : t'.inRange (rescale t.digits t'.digits a.1) = true)
    (hb : t'.inRange (rescale t.digits t'.digits b.1) = true) :
    le (explicit t' a) (explicit t' b) = true := by
  simp only [le, decide_eq_true_eq] at h ⊢
  simp only [explicit, wrap, wrapInt_of_inRange ha, wrapInt_of_inRange hb]
  exact rescale_mono _ _ h

/-! ### Implicit conversions keep value and order -/

theorem implicit_le (h : t.subsumes t' = true) (a b : Fx t) :
    le (implicit h a) (implicit h b) = le a b := by
  have hc : (0 : Int) < 10 ^ (t'.digits - t.digits) := Int.pow_pos (by decide)
  simp only [le, implicit]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hl
    exact Int.le_of_mul_le_mul_right hl hc
  · intro hl
    exact Int.mul_le_mul_of_nonneg_right hl (Int.le_of_lt hc)

theorem implicit_injective (h : t.subsumes t' = true) {a b : Fx t}
    (he : implicit h a = implicit h b) : a = b := by
  have hc : (10 : Int) ^ (t'.digits - t.digits) ≠ 0 := pow_ten_ne _
  apply Subtype.ext
  have hv : a.1 * 10 ^ (t'.digits - t.digits) = b.1 * 10 ^ (t'.digits - t.digits) :=
    congrArg Subtype.val he
  exact Int.eq_of_mul_eq_mul_right hc hv

end Fx

/-! ### The implicit conversion is the range-contained one -/

namespace FxTy

/-- A range-contained pair passes solc's own test, so `implicitOK` is just
`subsumes`. -/
theorem solcImplicit_of_subsumes {t t' : FxTy} (h : t.subsumes t' = true) :
    t.solcImplicit t' = true := by
  simp only [subsumes, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hd, hlo1, _⟩, _, hhi2⟩ := h
  have hP : (0 : Int) < 10 ^ (t'.digits - t.digits) := Int.pow_pos (by decide)
  have hs : 0 < t.scale := t.scale_pos
  have hs' : t'.scale = 10 ^ (t'.digits - t.digits) * t.scale := by
    simp only [scale]
    rw [← Int.pow_add, Nat.sub_add_cancel hd]
  have hl : t.lo ≤ 0 := t.lo_le_zero
  have hh : 0 ≤ t.hi := t.hi_nonneg
  -- the integer parts
  have hmax : t.maxInt ≤ t'.maxInt := by
    simp only [maxInt]
    have e : t.hi / t.scale =
        (10 ^ (t'.digits - t.digits) * t.hi) / (10 ^ (t'.digits - t.digits) * t.scale) :=
      (Int.mul_ediv_mul_of_pos t.hi t.scale hP).symm
    rw [e, ← hs']
    exact Int.ediv_le_ediv t'.scale_pos (by rw [Int.mul_comm]; exact hhi2)
  have hmin : t'.minInt ≤ t.minInt := by
    simp only [minInt]
    have e : (-t.lo) / t.scale =
        (10 ^ (t'.digits - t.digits) * (-t.lo)) / (10 ^ (t'.digits - t.digits) * t.scale) :=
      (Int.mul_ediv_mul_of_pos (-t.lo) t.scale hP).symm
    have hle : 10 ^ (t'.digits - t.digits) * (-t.lo) ≤ -t'.lo := by
      rw [Int.mul_neg, Int.mul_comm]; omega
    have hq : (10 ^ (t'.digits - t.digits) * (-t.lo)) / t'.scale ≤ (-t'.lo) / t'.scale :=
      Int.ediv_le_ediv t'.scale_pos hle
    rw [← hs'] at e
    omega
  -- the widths
  have hhi : t.hi ≤ t'.hi := by
    have h1 : t.hi * 1 ≤ t.hi * 10 ^ (t'.digits - t.digits) :=
      Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ 10 ^ (t'.digits - t.digits) by omega) hh
    rw [Int.mul_one] at h1
    omega
  have hb : t.bits ≤ t'.bits := by
    have hp : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := t.pow_bits
    have hp' : (2 : Int) ^ t'.bits = 2 * 2 ^ (t'.bits - 1) := t'.pow_bits
    have g : 8 ≤ t.bits := t.bits_ge
    have g' : 8 ≤ t'.bits := t'.bits_ge
    have hh2 : (0 : Int) < 2 ^ (t.bits - 1) := t.half_pos
    revert hlo1 hhi
    simp only [lo, hi]
    cases t.signed <;> cases t'.signed <;>
      simp only [Bool.false_eq_true, if_false, if_true] <;> intro hlo1 hhi
    · exact pow_two_le (by omega)
    · have hb1 : t.bits ≤ t'.bits - 1 := pow_two_le (by omega)
      omega
    · have hneg : -(2 : Int) ^ (t.bits - 1) * 10 ^ (t'.digits - t.digits) < 0 :=
        Int.mul_neg_of_neg_of_pos (by omega) hP
      omega
    · have hb1 : t.bits - 1 ≤ t'.bits - 1 := pow_two_le (by omega)
      omega
  simp only [solcImplicit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hd, hb⟩, hmax⟩, hmin⟩

/-- The implicit conversion test is exactly `subsumes`. -/
theorem implicitOK_iff {t t' : FxTy} : t.implicitOK t' = true ↔ t.subsumes t' = true := by
  simp only [implicitOK, Bool.and_eq_true]
  exact ⟨fun h => h.2, fun h => ⟨solcImplicit_of_subsumes h, h⟩⟩

theorem lo_inRange (t : FxTy) : t.inRange t.lo = true := by
  have h1 : (0 : Int) < 2 ^ (t.bits - 1) := t.half_pos
  have h2 : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := t.pow_bits
  simp only [inRange, lo, hi, Bool.and_eq_true, decide_eq_true_eq]
  split <;> omega

theorem hi_inRange (t : FxTy) : t.inRange t.hi = true := by
  have h1 : (0 : Int) < 2 ^ (t.bits - 1) := t.half_pos
  have h2 : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := t.pow_bits
  simp only [inRange, lo, hi, Bool.and_eq_true, decide_eq_true_eq]
  split <;> omega

/-- `subsumes` is range containment: it holds exactly when every value of
`t` is a value of `t'`. -/
theorem subsumes_iff {t t' : FxTy} :
    t.subsumes t' = true ↔ ∀ a : Fx t, ∃ b : Fx t', Fx.SameValue a b := by
  constructor
  · intro h a
    exact ⟨Fx.implicit h a, Fx.implicit_sameValue h a⟩
  · intro h
    have hs : 0 < t.scale := t.scale_pos
    have hs1 : 0 < t'.scale := t'.scale_pos
    -- the least unit of `t` forces the digits
    have hd : t.digits ≤ t'.digits := by
      have h1 : t.inRange 1 = true := by
        have hg : 8 ≤ t.bits := t.bits_ge
        have hbn : (2 : Nat) ^ 7 ≤ 2 ^ (t.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        have e : ((2 ^ (t.bits - 1) : Nat) : Int) = (2 : Int) ^ (t.bits - 1) := Int.natCast_pow 2 _
        have hp : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := t.pow_bits
        have h7 : (2 : Nat) ^ 7 = 128 := by decide
        simp only [inRange, lo, hi, Bool.and_eq_true, decide_eq_true_eq]
        split <;> omega
      obtain ⟨b, hb⟩ := h ⟨1, h1⟩
      simp only [Fx.SameValue, Int.one_mul] at hb
      apply Nat.le_of_not_lt
      intro hlt
      have hlt' : t'.scale < t.scale := by
        simp only [scale]
        have e1 : ((10 ^ t'.digits : Nat) : Int) = (10 : Int) ^ t'.digits := Int.natCast_pow 10 _
        have e2 : ((10 ^ t.digits : Nat) : Int) = (10 : Int) ^ t.digits := Int.natCast_pow 10 _
        have hn : 10 ^ t'.digits < 10 ^ t.digits := Nat.pow_lt_pow_right (by decide) hlt
        omega
      by_cases hb0 : 0 < b.1
      · have hge : 1 * t.scale ≤ b.1 * t.scale := Int.mul_le_mul_of_nonneg_right hb0 (by omega)
        omega
      · have hle : b.1 * t.scale ≤ 0 * t.scale :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        omega
    have hs' : t'.scale = 10 ^ (t'.digits - t.digits) * t.scale := by
      simp only [scale]
      rw [← Int.pow_add, Nat.sub_add_cancel hd]
    -- an endpoint's image is its rescaled integer
    have hend : ∀ a : Fx t, t'.inRange (a.1 * 10 ^ (t'.digits - t.digits)) = true := by
      intro a
      obtain ⟨b, hb⟩ := h a
      simp only [Fx.SameValue] at hb
      have he : a.1 * 10 ^ (t'.digits - t.digits) = b.1 := by
        apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hs)
        rw [← hb, hs', Int.mul_assoc]
      rw [he]
      exact b.2
    simp only [subsumes, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hd, hend ⟨t.lo, t.lo_inRange⟩⟩, hend ⟨t.hi, t.hi_inRange⟩⟩

/-- Every type converts implicitly to itself. -/
theorem subsumes_refl (t : FxTy) : t.subsumes t = true := by
  simp only [subsumes, Nat.le_refl, decide_true, Nat.sub_self, Int.pow_zero, Int.mul_one,
    t.lo_inRange, t.hi_inRange, Bool.and_self]

/-- The common type of a binary operation is one both operands convert to
implicitly. -/
theorem common?_subsumes {t t' u : FxTy} (h : common? t t' = some u) :
    t.subsumes u = true ∧ t'.subsumes u = true := by
  unfold common? at h
  by_cases h1 : implicitOK t' t = true
  · simp only [h1, if_true, Option.some.injEq] at h
    subst h
    exact ⟨subsumes_refl t, implicitOK_iff.mp h1⟩
  · by_cases h2 : implicitOK t t' = true
    · simp only [h1, Bool.false_eq_true, if_false, h2, if_true, Option.some.injEq] at h
      subst h
      exact ⟨implicitOK_iff.mp h2, subsumes_refl t'⟩
    · simp only [h1, h2, Bool.false_eq_true, if_false] at h
      exact nomatch h

end FxTy

namespace Fx

variable {t t' : FxTy}

/-- An implicit conversion (`implicitOK`) keeps the value, the order and
distinctness. -/
theorem implicit_preserves (h : t.implicitOK t' = true) (a b : Fx t) :
    SameValue a (implicit (FxTy.implicitOK_iff.mp h) a) ∧
    lt (implicit (FxTy.implicitOK_iff.mp h) a) (implicit (FxTy.implicitOK_iff.mp h) b) =
      lt a b ∧
    le (implicit (FxTy.implicitOK_iff.mp h) a) (implicit (FxTy.implicitOK_iff.mp h) b) =
      le a b ∧
    (implicit (FxTy.implicitOK_iff.mp h) a = implicit (FxTy.implicitOK_iff.mp h) b ↔ a = b) :=
  ⟨implicit_sameValue _ a, implicit_lt _ a b, implicit_le _ a b,
    ⟨implicit_injective _, fun he => he ▸ rfl⟩⟩

/-- Both operands of a binary operation keep their values at the common
type. -/
theorem common?_preserves {u : FxTy} (h : FxTy.common? t t' = some u) (a : Fx t) (b : Fx t') :
    SameValue a (implicit (FxTy.common?_subsumes h).1 a) ∧
    SameValue b (implicit (FxTy.common?_subsumes h).2 b) :=
  ⟨implicit_sameValue _ a, implicit_sameValue _ b⟩

end Fx

/-- `*` is not associative under truncation: at `ufixed16x2`,
`(0.01 · 0.50) · 2.00 = 0.00` but `0.01 · (0.50 · 2.00) = 0.01`. -/
example :
    ((Fx.mul .checked (⟨1, by decide⟩ : Fx Fx.ufixed16x2) ⟨50, by decide⟩).toOption.bind
        fun r => (Fx.mul .checked r ⟨200, by decide⟩).toOption).map Subtype.val = some 0 ∧
    ((Fx.mul .checked (⟨50, by decide⟩ : Fx Fx.ufixed16x2) ⟨200, by decide⟩).toOption.bind
        fun r => (Fx.mul .checked ⟨1, by decide⟩ r).toOption).map Subtype.val = some 1 := by
  decide

/-! ### Axiom pins -/

/--
info: 'Solidity.Language.FixedPoint.FxTy.implicitOK_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FxTy.implicitOK_iff

/--
info: 'Solidity.Language.FixedPoint.FxTy.subsumes_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FxTy.subsumes_iff

/--
info: 'Solidity.Language.FixedPoint.Fx.result_unchecked_of_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.result_unchecked_of_checked

/--
info: 'Solidity.Language.FixedPoint.Fx.mul_trunc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.mul_trunc

/--
info: 'Solidity.Language.FixedPoint.Fx.div_trunc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.div_trunc

/--
info: 'Solidity.Language.FixedPoint.Fx.explicit_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.explicit_explicit

/--
info: 'Solidity.Language.FixedPoint.Fx.implicit_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.implicit_preserves

/--
info: 'Solidity.Language.FixedPoint.Fx.neg_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.neg_unsigned

/--
info: 'Solidity.Language.FixedPoint.tdiv_tdiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tdiv_tdiv

end Solidity.Language.FixedPoint
