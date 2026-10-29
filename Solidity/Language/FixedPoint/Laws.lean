import Solidity.Language.FixedPoint

/-!
# Fixed-point laws

The laws of `Solidity/Language/FixedPoint.lean` the reviews of the
second-round decisions asked for (`docs/feature-work/fixed-point-semantics.md`,
§6): checked and unchecked arithmetic agree wherever the checked one
succeeds; `*` and `/` are exact when the exact result has at most `N` digits
and otherwise truncate toward zero by less than one unit in the last place;
lossless conversions round-trip; the implicit conversion is exactly the
range-contained one (`FxTy.implicitOK_iff`, which closes the earlier open
implication `subsumes → solcImplicit`) and keeps the value.
-/

namespace Solidity.Language.FixedPoint

/-! ### Truncating division -/

/-- `tdiv` by a positive divisor truncates toward zero: `q·d` lies between
`0` and `x`, less than one `d` away from `x`. -/
theorem tdiv_trunc (x d : Int) (hd : 0 < d) :
    (0 ≤ x → x.tdiv d * d ≤ x ∧ x < x.tdiv d * d + d) ∧
    (x < 0 → x.tdiv d * d - d < x ∧ x ≤ x.tdiv d * d) := by
  have he : x.tmod d + x.tdiv d * d = x := Int.tmod_add_tdiv_mul x d
  have h1 : x.tmod d < d := Int.tmod_lt_of_pos x hd
  have h2 : -d < x.tmod d := Int.lt_tmod_of_pos x hd
  have hb := Fx.tmod_between x d
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have := (hb.1 hx).1; omega
  · have := (hb.2 hx).2; omega

/-- The remainder of a truncating division by any nonzero `b` has the sign
of the dividend and is smaller than `b` in magnitude. -/
theorem tdiv_rem (x b : Int) (hb : b ≠ 0) :
    x = x.tdiv b * b + x.tmod b ∧ (x.tmod b).natAbs < b.natAbs ∧
    (0 ≤ x → 0 ≤ x.tmod b) ∧ (x < 0 → x.tmod b ≤ 0) := by
  have he : x.tmod b + x.tdiv b * b = x := Int.tmod_add_tdiv_mul x b
  have hn : (x.tmod b).natAbs = x.natAbs % b.natAbs := Int.natAbs_tmod x b
  have hpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hlt : x.natAbs % b.natAbs < b.natAbs := Nat.mod_lt _ hpos
  have hs := Fx.tmod_between x b
  refine ⟨by omega, by omega, fun hx => (hs.1 hx).1, fun hx => (hs.2 hx).2⟩

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
  by_cases hb : b.1 = 0
  · simp only [div, hb, if_true] at h
    exact nomatch h
  · simp only [div, hb, if_false] at h ⊢
    exact result_unchecked_of_checked h

theorem mod_agree {a b : Fx t} {r : Fx t} (h : mod .checked a b = .ok r) :
    mod .unchecked a b = .ok r := by
  by_cases hb : b.1 = 0
  · simp only [mod, hb, if_true] at h
    exact nomatch h
  · simp only [mod, hb, if_false] at h ⊢
    exact result_unchecked_of_checked h

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

/-! ### `*` and `/`: exact, then truncated toward zero -/

/-- A checked product is the exact product truncated toward zero: `r·10^N`
lies between `0` and `a·b`, less than one `10^N` away (an error below one
unit in the last place, Q3, Q8). -/
theorem mul_trunc {a b r : Fx t} (h : mul .checked a b = .ok r) :
    (0 ≤ a.1 * b.1 → r.1 * t.scale ≤ a.1 * b.1 ∧ a.1 * b.1 < r.1 * t.scale + t.scale) ∧
    (a.1 * b.1 < 0 → r.1 * t.scale - t.scale < a.1 * b.1 ∧ a.1 * b.1 ≤ r.1 * t.scale) := by
  have hr : r.1 = (a.1 * b.1).tdiv t.scale := result_checked_val h
  rw [hr]
  exact tdiv_trunc _ _ t.scale_pos

/-- A product whose exact value has at most `N` digits is exact. -/
theorem mul_exact {a b r : Fx t} (h : mul .checked a b = .ok r)
    (hd : t.scale ∣ a.1 * b.1) : r.1 * t.scale = a.1 * b.1 := by
  have hr : r.1 = (a.1 * b.1).tdiv t.scale := result_checked_val h
  rw [hr]
  exact Int.tdiv_mul_cancel hd

/-- A checked quotient is the exact quotient truncated toward zero:
`a·10^N = r·b + e` with `|e| < |b|` and `e` of the sign of `a` (Q3, Q8). -/
theorem div_trunc {a b r : Fx t} (h : div .checked a b = .ok r) :
    b.1 ≠ 0 ∧ ∃ e : Int, a.1 * t.scale = r.1 * b.1 + e ∧ e.natAbs < b.1.natAbs ∧
      (0 ≤ a.1 → 0 ≤ e) ∧ (a.1 < 0 → e ≤ 0) := by
  by_cases hb : b.1 = 0
  · simp only [div, hb, if_true] at h
    exact nomatch h
  · simp only [div, hb, if_false] at h
    have hr : r.1 = (a.1 * t.scale).tdiv b.1 := result_checked_val h
    have hs := t.scale_pos
    have hq := tdiv_rem (a.1 * t.scale) b.1 hb
    refine ⟨hb, (a.1 * t.scale).tmod b.1, ?_, hq.2.1, fun ha => ?_, fun ha => ?_⟩
    · rw [hr]; exact hq.1
    · exact hq.2.2.1 (Int.mul_nonneg ha (by omega))
    · exact hq.2.2.2 (Int.mul_neg_of_neg_of_pos ha hs)

/-- A quotient whose exact value has at most `N` digits is exact. -/
theorem div_exact {a b r : Fx t} (h : div .checked a b = .ok r)
    (hd : b.1 ∣ a.1 * t.scale) : r.1 * b.1 = a.1 * t.scale := by
  by_cases hb : b.1 = 0
  · simp only [div, hb, if_true] at h
    exact nomatch h
  · simp only [div, hb, if_false] at h
    have hr : r.1 = (a.1 * t.scale).tdiv b.1 := result_checked_val h
    rw [hr]
    exact Int.tdiv_mul_cancel hd

/-- `++` and `--` move the value by exactly `1`. -/
theorem inc_val {a r : Fx t} (h : inc .checked a = .ok r) : r.1 = a.1 + t.scale :=
  result_checked_val h

theorem dec_val {a r : Fx t} (h : dec .checked a = .ok r) : r.1 = a.1 - t.scale :=
  result_checked_val h

/-! ### Lossless conversions round-trip -/

/-- Rescaling up and back down is the identity. -/
theorem rescale_up_down (n n' : Nat) (h : n ≤ n') (v : Int) :
    rescale n' n (rescale n n' v) = v := by
  have hp : (10 : Int) ^ (n' - n) ≠ 0 := by
    have : (0 : Int) < 10 ^ (n' - n) := Int.pow_pos (by decide)
    omega
  by_cases he : n' ≤ n
  · have hnn : n = n' := Nat.le_antisymm h he
    subst hnn
    simp only [rescale, Nat.le_refl, if_true, Nat.sub_self, Int.pow_zero, Int.mul_one]
  · simp only [rescale, h, if_true, he, if_false]
    exact Int.mul_tdiv_cancel v hp

/-- An implicit conversion followed by the explicit conversion back gives
the value back. -/
theorem explicit_implicit (h : t.subsumes t' = true) (a : Fx t) :
    explicit t (implicit h a) = a := by
  have hd : t.digits ≤ t'.digits := by
    simp only [FxTy.subsumes, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hr : rescale t'.digits t.digits (a.1 * 10 ^ (t'.digits - t.digits)) = a.1 := by
    have := rescale_up_down t.digits t'.digits hd a.1
    simp only [rescale, hd, if_true] at this
    exact this
  apply Subtype.ext
  simp only [explicit, implicit, wrap, hr, wrapInt_of_inRange a.2]

/-- An integer converted explicitly and converted back gives the integer
back, when its scaled value is in range. -/
theorem toIntTrunc_ofIntegerExplicit (k : Int) (h : t.inRange (k * t.scale) = true) :
    toIntTrunc (ofIntegerExplicit t k) = k := by
  have hs := t.scale_pos
  simp only [toIntTrunc, ofIntegerExplicit, wrap, wrapInt_of_inRange h]
  exact Int.mul_tdiv_cancel k (by omega)

/-- The `M`-bit pattern of a value (the inverse of `ofBits`). -/
def toBits (a : Fx t) : Int := a.1 % 2 ^ t.bits

/-- A bit pattern read as a value and back is the bit pattern. -/
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

end Fx

/-! ### The implicit conversion is the range-contained one -/

namespace FxTy

theorem pow_two_le {m n : Nat} (h : (2 : Int) ^ m ≤ 2 ^ n) : m ≤ n := by
  have e1 : ((2 ^ m : Nat) : Int) = (2 : Int) ^ m := Int.natCast_pow 2 m
  have e2 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := Int.natCast_pow 2 n
  have hn : 2 ^ m ≤ 2 ^ n := by omega
  exact (Nat.pow_le_pow_iff_right (by decide)).mp hn

theorem lo_le_zero (t : FxTy) : t.lo ≤ 0 := by
  have := t.half_pos
  simp only [lo]; split <;> omega

theorem hi_nonneg (t : FxTy) : 0 ≤ t.hi := by
  have := t.half_pos
  have := t.pow_bits
  simp only [hi]; split <;> omega

/-- A range-contained pair passes solc's own test: `implicitOK` is just
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
  have hl := t.lo_le_zero
  have hh := t.hi_nonneg
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
    have := Int.ediv_le_ediv t'.scale_pos hle
    rw [← hs'] at e
    omega
  -- the widths
  have hhi : t.hi ≤ t'.hi := by
    have : t.hi ≤ t.hi * 10 ^ (t'.digits - t.digits) := by
      have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ 10 ^ (t'.digits - t.digits) by omega) hh
      rw [Int.mul_one] at this; exact this
    omega
  have hb : t.bits ≤ t'.bits := by
    have hp := t.pow_bits
    have hp' := t'.pow_bits
    have g := t.bits_ge
    have g' := t'.bits_ge
    revert hlo1 hhi
    simp only [lo, hi]
    cases t.signed <;> cases t'.signed <;>
      simp only [Bool.false_eq_true, if_false, if_true] <;> intro hlo1 hhi
    · exact pow_two_le (by omega)
    · have : t.bits ≤ t'.bits - 1 := pow_two_le (by omega)
      omega
    · have := t.half_pos
      have : -(2 : Int) ^ (t.bits - 1) * 10 ^ (t'.digits - t.digits) < 0 :=
        Int.mul_neg_of_neg_of_pos (by omega) hP
      omega
    · have : t.bits - 1 ≤ t'.bits - 1 := pow_two_le (by omega)
      omega
  simp only [solcImplicit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hd, hb⟩, hmax⟩, hmin⟩

/-- The implicit conversion test is exactly range containment. -/
theorem implicitOK_iff {t t' : FxTy} : t.implicitOK t' = true ↔ t.subsumes t' = true := by
  simp only [implicitOK, Bool.and_eq_true]
  exact ⟨fun h => h.2, fun h => ⟨solcImplicit_of_subsumes h, h⟩⟩

/-- Every type converts implicitly to itself. -/
theorem subsumes_refl (t : FxTy) : t.subsumes t = true := by
  have hl := (show t.inRange t.lo = true by
    have := t.half_pos; have := t.pow_bits
    simp only [inRange, lo, hi, Bool.and_eq_true, decide_eq_true_eq]
    split <;> omega)
  have hh := (show t.inRange t.hi = true by
    have := t.half_pos; have := t.pow_bits
    simp only [inRange, lo, hi, Bool.and_eq_true, decide_eq_true_eq]
    split <;> omega)
  simp only [subsumes, Nat.le_refl, decide_true, Nat.sub_self, Int.pow_zero, Int.mul_one,
    hl, hh, Bool.and_self]

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

/-- An implicit conversion (`implicitOK`) keeps the value and the order. -/
theorem implicit_preserves (h : t.implicitOK t' = true) (a b : Fx t) :
    SameValue a (implicit (FxTy.implicitOK_iff.mp h) a) ∧
    lt (implicit (FxTy.implicitOK_iff.mp h) a) (implicit (FxTy.implicitOK_iff.mp h) b) =
      lt a b :=
  ⟨implicit_sameValue _ a, implicit_lt _ a b⟩

/-- Both operands of a binary operation keep their values at the common
type. -/
theorem common?_preserves {u : FxTy} (h : FxTy.common? t t' = some u) (a : Fx t) (b : Fx t') :
    SameValue a (implicit (FxTy.common?_subsumes h).1 a) ∧
    SameValue b (implicit (FxTy.common?_subsumes h).2 b) :=
  ⟨implicit_sameValue _ a, implicit_sameValue _ b⟩

end Fx

/-! ### Axiom pins -/

/--
info: 'Solidity.Language.FixedPoint.FxTy.implicitOK_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FxTy.implicitOK_iff

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
info: 'Solidity.Language.FixedPoint.Fx.explicit_implicit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.explicit_implicit

/--
info: 'Solidity.Language.FixedPoint.Fx.implicit_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.implicit_preserves

end Solidity.Language.FixedPoint
