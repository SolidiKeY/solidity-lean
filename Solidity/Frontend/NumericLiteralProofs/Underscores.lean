import Solidity.Frontend.NumericLiteralProofs.Refusals

/-! # Global decimal underscore placement, including fractions and exponents -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

/-- Every underscore has an immediately following decimal digit. -/
def underscoreOk : Bytes → Bool
  | [] => true
  | b :: r =>
    if b.toNat == 95 then (r.head?.map isDigit |>.getD false) && underscoreOk r
    else underscoreOk r

theorem digit_marker_false {b : UInt8} (hd : isDigit b = true) :
    (b.toNat == 95) = false := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  apply Bool.eq_false_iff.mpr
  intro hb
  have he : b.toNat = 95 := beq_iff_eq.mp hb
  omega

theorem Tail.underscore_ok {raw ds rest : Bytes} (h : Tail raw ds rest)
    (hs : underscoreOk rest = true) : underscoreOk raw = true := by
  induction h with
  | nil => rfl
  | digit hd _ ih =>
    simp only [underscoreOk, digit_marker_false hd, Bool.false_eq_true, ↓reduceIte]
    exact ih hs
  | separated hd hu hc _ ih =>
    simp only [underscoreOk, hu, ↓reduceIte, List.head?_cons, Option.map_some,
      Option.getD_some, hc, digit_marker_false hc, Bool.false_eq_true, Bool.true_and]
    exact ih hs
  | other _ _ => exact hs
  | finalUnderscore _ _ => exact hs
  | badUnderscore _ _ _ => exact hs

theorem Digits.underscore_ok {raw ds rest : Bytes} (h : Digits raw ds rest)
    (hs : underscoreOk rest = true) : underscoreOk raw = true := by
  cases h with
  | first hd ht =>
    simp only [underscoreOk, digit_marker_false hd, Bool.false_eq_true, ↓reduceIte]
    exact ht.underscore_ok hs

theorem Exponent.underscore_ok {raw : Bytes} {e : Int} (h : Exponent raw e) :
    underscoreOk raw = true := by
  cases h with
  | absent => rfl
  | unsigned he hd =>
    simp only [underscoreOk, (exponent_marker he).2.1, Bool.false_eq_true, ↓reduceIte]
    exact hd.underscore_ok rfl
  | negative he hd =>
    simp only [underscoreOk, (exponent_marker he).2.1, Bool.false_eq_true, ↓reduceIte]
    exact hd.underscore_ok rfl

theorem FractionPart.underscore_ok {raw ds rest : Bytes} {e : Int}
    (h : FractionPart raw ds rest) (he : Exponent rest e) : underscoreOk raw = true := by
  cases h with
  | nil => rfl
  | absent _ => exact he.underscore_ok
  | present hd =>
    change underscoreOk _ = true
    exact hd.underscore_ok he.underscore_ok

theorem Decimal.underscore_ok {raw : Bytes} {n : NumLit} (h : Decimal raw n) :
    underscoreOk raw = true := by
  cases h with
  | mk hi hf _ _ he =>
    cases hi with
    | absent _ => exact hf.underscore_ok he
    | present hd => exact hd.underscore_ok (hf.underscore_ok he)

theorem underscoreOk_trailing (pre : Bytes) : underscoreOk (pre ++ [95]) = false := by
  induction pre with
  | nil => rfl
  | cons b pre ih =>
    simp only [List.cons_append, underscoreOk, ih, Bool.and_false, ite_self]

theorem underscoreOk_doubled (pre post : Bytes) :
    underscoreOk (pre ++ 95 :: 95 :: post) = false := by
  induction pre with
  | nil => rfl
  | cons b pre ih =>
    simp only [List.cons_append, underscoreOk, ih, Bool.and_false, ite_self]

/-- Arbitrary byte prefixes, including fractional and exponent spellings. -/
theorem decimal_trailing_underscore_refused (pre : Bytes) : decNumber (pre ++ [95]) = none := by
  cases h : decNumber (pre ++ [95]) with
  | none => rfl
  | some n =>
    have hg := (Decimal.complete h).underscore_ok
    rw [underscoreOk_trailing] at hg
    cases hg

/-- Arbitrary doubled-underscore position in any would-be decimal spelling. -/
theorem decimal_doubled_underscore_refused (pre post : Bytes) :
    decNumber (pre ++ 95 :: 95 :: post) = none := by
  cases h : decNumber (pre ++ 95 :: 95 :: post) with
  | none => rfl
  | some n =>
    have hg := (Decimal.complete h).underscore_ok
    rw [underscoreOk_doubled] at hg
    cases hg

theorem decimal_leading_underscore_refused (rest : Bytes) : decNumber (95 :: rest) = none := rfl

theorem decimal_fraction_underscore_refused {raw ds : Bytes} (hd : Digits raw ds [])
    (rest : Bytes) : decNumber (raw ++ 46 :: 95 :: rest) = none :=
  missing_fraction_refused (.present (hd.append_stop rfl (.other (by decide) (by decide))))
    (.other (by decide))

theorem underscoreOk_bad_follower (pre post : Bytes) (b : UInt8) (hb : isDigit b = false) :
    underscoreOk (pre ++ 95 :: b :: post) = false := by
  induction pre with
  | nil =>
    change (isDigit b && underscoreOk (b :: post)) = false
    rw [hb]; rfl
  | cons c pre ih =>
    simp only [List.cons_append, underscoreOk, ih, Bool.and_false, ite_self]

theorem decimal_bad_underscore_follower_refused (pre post : Bytes) (b : UInt8)
    (hb : isDigit b = false) : decNumber (pre ++ 95 :: b :: post) = none := by
  cases h : decNumber (pre ++ 95 :: b :: post) with
  | none => rfl
  | some n =>
    have hg := (Decimal.complete h).underscore_ok
    rw [underscoreOk_bad_follower pre post b hb] at hg
    cases hg

theorem decimal_bad_exponent {raw ip r1 fp r2 : Bytes}
    (hi : IntegerPart raw ip r1) (hf : FractionPart r1 fp r2)
    (he : readExponent r2 = none) : decNumber raw = none := by
  rw [decNumber_parts hi, hf.sound]
  simp only [he, Option.map_none, ite_self]

theorem decimal_exponent_underscore_refused {raw ip r1 fp rest : Bytes} {e : UInt8}
    (hi : IntegerPart raw ip r1) (hf : FractionPart r1 fp (e :: 95 :: rest))
    (he : e.toNat = 101 ∨ e.toNat = 69) : decNumber raw = none := by
  apply decimal_bad_exponent hi hf
  have he' : (e.toNat == 101 || e.toNat == 69) = true := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using he
  simp only [readExponent, he', ↓reduceIte, digits1]
  rfl

theorem decimal_negative_exponent_underscore_refused {raw ip r1 fp rest : Bytes} {e : UInt8}
    (hi : IntegerPart raw ip r1) (hf : FractionPart r1 fp (e :: 45 :: 95 :: rest))
    (he : e.toNat = 101 ∨ e.toNat = 69) : decNumber raw = none := by
  apply decimal_bad_exponent hi hf
  have he' : (e.toNat == 101 || e.toNat == 69) = true := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using he
  simp only [readExponent, he', ↓reduceIte, digits1]
  rfl

theorem decimal_plus_exponent_refused {raw ip r1 fp rest : Bytes} {e : UInt8}
    (hi : IntegerPart raw ip r1) (hf : FractionPart r1 fp (e :: 43 :: rest))
    (he : e.toNat = 101 ∨ e.toNat = 69) : decNumber raw = none := by
  apply decimal_bad_exponent hi hf
  have he' : (e.toNat == 101 || e.toNat == 69) = true := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using he
  simp only [readExponent, he', ↓reduceIte, digits1]
  rfl

end Solidity.Frontend.NumericLiteralProofs
