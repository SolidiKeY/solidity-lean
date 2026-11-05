import Solidity.Frontend.NumericLiteralProofs.Values

/-! # Arbitrary-length refusal and suffix-consumption consequences -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

/-- A decoded leading zero followed by another digit is refused, regardless
of how long the spelling, fraction, exponent or leftover suffix is. -/
theorem octal_refused {raw rest ds : Bytes} {b : UInt8}
    (hd : Digits raw (48 :: b :: ds) rest) : decNumber raw = none := by
  rw [decNumber_parts (.present hd)]
  have ho : ((48 :: b :: ds).length > 1 && (48 :: b :: ds).head? == some 48) = true := by
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply decide_eq_true_eq.mpr
      simp only [List.length_cons]
      omega
    · rfl
  split
  · rfl
  · simp only [ho, ↓reduceIte, ite_self]

/-- A period reached after the integer must be followed by a digit. -/
theorem missing_fraction_refused {raw ip bad : Bytes}
    (hi : IntegerPart raw ip (46 :: bad)) (hb : NoDigits bad) : decNumber raw = none := by
  rw [decNumber_parts hi]
  simp only [readFraction, hb.sound]

/-- Any nonempty decimal tail result is exactly a consumed prefix followed
by the untouched suffix; the decoded value belongs to that prefix alone. -/
theorem digits1_exact_suffix {raw ds rest : Bytes}
    (h : digits1 raw = some (ds, rest)) :
    ∃ pre : Bytes, raw = pre ++ rest ∧ eraseUnderscores pre = ds ∧ pre ≠ [] :=
  (Digits.complete h).consumed

/-- A doubled underscore is retained intact, for any following bytes. -/
theorem doubled_underscore_tail (rest : Bytes) :
    digitsTail (95 :: 95 :: rest) = ([], 95 :: 95 :: rest) :=
  (Tail.badUnderscore (by decide) (by decide) (by decide)).sound

/-- A trailing underscore is retained rather than silently consumed. -/
theorem trailing_underscore_tail : digitsTail [95] = ([], [95]) :=
  (Tail.finalUnderscore (by decide) (by decide)).sound

/-- Leading underscore is forbidden for the mandatory first digit, no
matter how many bytes follow. The tail helper has a different contract. -/
theorem leading_underscore_digits (rest : Bytes) : digits1 (95 :: rest) = none :=
  (NoDigits.other (by decide)).sound

/-- Empty hexadecimal input and empty 0x body are refused. -/
theorem empty_hex_digits : hexDigits [] = none := rfl

theorem empty_hex_number : hexNumber [48, 120] = none := rfl

/-- Non-40-digit decoded spellings never set the checksum flag. -/
theorem eip55_other_length {ds : Bytes} (h : ds.length ≠ 40) : eip55 ds = false := by
  have hn : (ds.length == 40) = false := Bool.eq_false_iff.mpr (by
    intro hb; exact h (beq_iff_eq.mp hb))
  simp only [eip55, hn, Bool.false_and]

theorem decimal_bad_suffix {raw ds suffix : Bytes} (hd : Digits raw ds [])
    (hs : Tail suffix [] suffix) (hf : readFraction suffix = some ([], suffix))
    (he : readExponent suffix = none) : decNumber (raw ++ suffix) = none := by
  rw [decNumber_parts (.present (hd.append_stop rfl hs)), hf]
  simp only [he, Option.map_none, ite_self]

/-- Every complete decimal digit spelling refuses a trailing underscore. -/
theorem trailing_underscore_refused {raw ds : Bytes} (hd : Digits raw ds []) :
    decNumber (raw ++ [95]) = none :=
  decimal_bad_suffix hd (.finalUnderscore (by decide) (by decide)) rfl rfl

/-- Every complete digit spelling refuses a doubled underscore and arbitrary tail. -/
theorem doubled_underscore_refused {raw ds : Bytes} (hd : Digits raw ds []) (rest : Bytes) :
    decNumber (raw ++ 95 :: 95 :: rest) = none :=
  decimal_bad_suffix hd (.badUnderscore (by decide) (by decide) (by decide)) rfl rfl

/-- Missing unsigned exponent digits, with arbitrary complete mantissa length. -/
theorem missing_exponent_refused {raw ds : Bytes} (hd : Digits raw ds [])
    {e : UInt8} (he : e.toNat = 101 ∨ e.toNat = 69) :
    decNumber (raw ++ [e]) = none := by
  have hm := exponent_marker he
  apply decimal_bad_suffix hd (.other hm.1 hm.2.1)
  · exact (FractionPart.absent hm.2.2).sound
  · have he' : (e.toNat == 101 || e.toNat == 69) = true := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using he
    simp only [readExponent, he', ↓reduceIte, digits1]

/-- Minus exponents require a digit, even for an arbitrarily long bad remainder. -/
theorem missing_negative_exponent_refused {raw ds bad : Bytes} (hd : Digits raw ds [])
    {e : UInt8} (he : e.toNat = 101 ∨ e.toNat = 69) (hb : NoDigits bad) :
    decNumber (raw ++ e :: 45 :: bad) = none := by
  have hm := exponent_marker he
  apply decimal_bad_suffix hd (.other hm.1 hm.2.1)
  · exact (FractionPart.absent hm.2.2).sound
  · have he' : (e.toNat == 101 || e.toNat == 69) = true := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using he
    simp only [readExponent, he', ↓reduceIte, hb.sound]

/-- Every hexadecimal spelling ends with an admitted hexadecimal digit. -/
theorem HexDigits.last_digit {raw ds : Bytes} (h : HexDigits raw ds) :
    ∃ pre : Bytes, ∃ b : UInt8, raw = pre ++ [b] ∧ isHexDigit b = true := by
  induction h with
  | @single b hd => exact ⟨[], b, rfl, hd⟩
  | @adjacent b raw ds hd ht ih =>
    obtain ⟨pre, c, hr, hc⟩ := ih
    refine ⟨b :: pre, c, ?_, hc⟩
    rw [hr]; rfl
  | @separated b raw ds hd ht ih =>
    obtain ⟨pre, c, hr, hc⟩ := ih
    refine ⟨b :: 95 :: pre, c, ?_, hc⟩
    rw [hr]; rfl

theorem hex_leading_underscore_refused (rest : Bytes) : hexDigits (95 :: rest) = none := by
  cases h : hexDigits (95 :: rest) with
  | none => rfl
  | some ds =>
    have hd : isHexDigit 95 = true := (HexDigits.complete _ _ h).head
    change false = true at hd
    cases hd

theorem hex_trailing_underscore_refused (raw : Bytes) : hexDigits (raw ++ [95]) = none := by
  cases h : hexDigits (raw ++ [95]) with
  | none => rfl
  | some ds =>
    obtain ⟨pre, b, hr, hd⟩ := (HexDigits.complete _ _ h).last_digit
    have hl := congrArg List.getLast? hr
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hl
    subst b
    change false = true at hd
    cases hd

/-- No admitted hexadecimal spelling contains doubled underscores anywhere. -/
theorem HexDigits.no_doubled {raw ds : Bytes} (h : HexDigits raw ds) :
    ∀ pre post : Bytes, raw ≠ pre ++ 95 :: 95 :: post := by
  induction h with
  | single hd =>
    intro pre post he
    have hl := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  | @adjacent b raw ds hd ht ih =>
    intro pre post he
    cases pre with
    | nil => exact hex_digit_not_underscore hd (List.cons.inj he).1
    | cons c pre => exact ih pre post (List.cons.inj he).2
  | @separated b raw ds hd ht ih =>
    intro pre post he
    cases pre with
    | nil => exact hex_digit_not_underscore hd (List.cons.inj he).1
    | cons c pre =>
      have hr := (List.cons.inj he).2
      cases pre with
      | nil =>
        have hh := (List.cons.inj hr).2
        rw [hh] at ht
        exact hex_digit_not_underscore ht.head rfl
      | cons d pre => exact ih pre post (List.cons.inj hr).2

theorem hex_doubled_underscore_refused (pre post : Bytes) :
    hexDigits (pre ++ 95 :: 95 :: post) = none := by
  cases h : hexDigits (pre ++ 95 :: 95 :: post) with
  | none => rfl
  | some ds => exact False.elim ((HexDigits.complete _ _ h).no_doubled pre post rfl)

theorem hex_number_leading_underscore_refused (rest : Bytes) :
    hexNumber (48 :: 120 :: 95 :: rest) = none := by
  simp only [hexNumber, hex_leading_underscore_refused, Option.map_none]

theorem hex_number_trailing_underscore_refused (raw : Bytes) :
    hexNumber (48 :: 120 :: (raw ++ [95])) = none := by
  simp only [hexNumber, hex_trailing_underscore_refused, Option.map_none]

theorem hex_number_doubled_underscore_refused (pre post : Bytes) :
    hexNumber (48 :: 120 :: (pre ++ 95 :: 95 :: post)) = none := by
  simp only [hexNumber, hex_doubled_underscore_refused, Option.map_none]

theorem uppercase_hex_prefix_refused (raw : Bytes) : hexNumber (48 :: 88 :: raw) = none := rfl

theorem HexDigits.raw_classes {raw ds : Bytes} (h : HexDigits raw ds) :
    raw.all (fun b => isHexDigit b || b.toNat == 95) = true := by
  induction h with
  | single hd => simp only [List.all_cons, hd, Bool.true_or, List.all_nil, Bool.and_self]
  | adjacent hd ht ih => simp only [List.all_cons, hd, Bool.true_or, Bool.true_and, ih]
  | separated hd ht ih =>
    simp only [List.all_cons, hd, Bool.true_or, Bool.true_and, ih]
    rfl

theorem hex_invalid_byte_refused (pre post : Bytes) (b : UInt8)
    (hb : isHexDigit b = false) (hu : (b.toNat == 95) = false) :
    hexDigits (pre ++ b :: post) = none := by
  cases h : hexDigits (pre ++ b :: post) with
  | none => rfl
  | some ds =>
    have hg := (HexDigits.complete _ _ h).raw_classes
    simp only [List.all_append, List.all_cons, hb, hu, Bool.or_self, Bool.false_and,
      Bool.and_false, Bool.false_eq_true] at hg

end Solidity.Frontend.NumericLiteralProofs
