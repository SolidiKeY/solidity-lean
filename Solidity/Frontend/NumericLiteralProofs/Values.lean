import Solidity.Frontend.NumericLiteralProofs.Spellings

/-! # Whole-spelling erasure and exact numeric interpretation -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem marker_keep {b : UInt8} (hu : (b.toNat == 95) = false) :
    (b.toNat != 95) = true := by
  change (!(b.toNat == 95)) = true
  rw [hu]; rfl

theorem marker_stop {b : UInt8} {r : Bytes} (hd : isDigit b = false)
    (hu : (b.toNat == 95) = false) :
    Tail (eraseUnderscores (b :: r)) [] (eraseUnderscores (b :: r)) := by
  simp only [eraseUnderscores, List.filter_cons, marker_keep hu, ↓reduceIte]
  exact .other hd hu

theorem exponent_marker {b : UInt8} (he : b.toNat = 101 ∨ b.toNat = 69) :
    isDigit b = false ∧ (b.toNat == 95) = false ∧ b ≠ 46 := by
  have hd : isDigit b = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hh
    omega
  have hu : (b.toNat == 95) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hb : b.toNat = 95 := beq_iff_eq.mp hh
    omega
  refine ⟨hd, hu, ?_⟩
  intro hb; subst b; contradiction

theorem Exponent.erased_stop {raw : Bytes} {e : Int} (h : Exponent raw e) :
    Tail (eraseUnderscores raw) [] (eraseUnderscores raw) := by
  cases h with
  | absent => exact .nil
  | unsigned he _ => exact marker_stop (exponent_marker he).1 (exponent_marker he).2.1
  | negative he _ => exact marker_stop (exponent_marker he).1 (exponent_marker he).2.1

theorem Exponent.erasure {raw : Bytes} {e : Int} (h : Exponent raw e) :
    Exponent (eraseUnderscores raw) e := by
  cases h with
  | absent => exact .absent
  | unsigned he hd =>
    simp only [eraseUnderscores, List.filter_cons,
      marker_keep (exponent_marker he).2.1, ↓reduceIte]
    exact .unsigned he (hd.erasure .nil)
  | negative he hd =>
    simp only [eraseUnderscores, List.filter_cons,
      marker_keep (exponent_marker he).2.1, ↓reduceIte]
    exact .negative he (hd.erasure .nil)

theorem Exponent.fraction_absent {raw : Bytes} {e : Int} (h : Exponent raw e) :
    FractionPart raw [] raw := by
  cases h with
  | absent => exact .nil
  | unsigned he _ => exact .absent (exponent_marker he).2.2
  | negative he _ => exact .absent (exponent_marker he).2.2

theorem FractionPart.erased_stop {raw ds rest : Bytes} {e : Int}
    (h : FractionPart raw ds rest) (he : Exponent rest e) :
    Tail (eraseUnderscores raw) [] (eraseUnderscores raw) := by
  cases h with
  | nil => exact .nil
  | absent _ => exact he.erased_stop
  | present _ => exact marker_stop (by decide) (by decide)

theorem FractionPart.erasure {raw ds rest : Bytes} {e : Int}
    (h : FractionPart raw ds rest) (he : Exponent rest e) :
    FractionPart (eraseUnderscores raw) ds (eraseUnderscores rest) := by
  cases h with
  | nil => exact .nil
  | absent _ => exact he.erasure.fraction_absent
  | present hd =>
    change FractionPart (46 :: eraseUnderscores _) _ _
    exact .present (hd.erasure he.erased_stop)

theorem NoDigits.of_stop {raw : Bytes} (h : Tail raw [] raw) : NoDigits raw := by
  cases h with
  | nil => exact .nil
  | other hd _ => exact .other hd
  | finalUnderscore hd _ => exact .other hd
  | badUnderscore hd _ _ => exact .other hd

theorem IntegerPart.erasure {raw ds rest fp r2 : Bytes} {e : Int}
    (h : IntegerPart raw ds rest) (hf : FractionPart rest fp r2) (he : Exponent r2 e) :
    IntegerPart (eraseUnderscores raw) ds (eraseUnderscores rest) := by
  cases h with
  | absent _ => exact .absent (NoDigits.of_stop (hf.erased_stop he))
  | present hd => exact .present (hd.erasure (hf.erased_stop he))

/-- Whole decimal erasure preserves every NumLit field, not merely its value. -/
theorem Decimal.erasure {raw : Bytes} {n : NumLit} (h : Decimal raw n) :
    Decimal (eraseUnderscores raw) n := by
  cases h with
  | mk hi hf hn ho he =>
    exact .mk (hi.erasure hf he) (hf.erasure he) hn ho he.erasure

theorem decNumber_erasure {raw : Bytes} {n : NumLit} (h : decNumber raw = some n) :
    decNumber (eraseUnderscores raw) = some n :=
  (Decimal.complete h).erasure.sound

theorem HexDigits.canonical {raw ds : Bytes} (h : HexDigits raw ds) : HexDigits ds ds := by
  induction h with
  | single hd => exact .single hd
  | adjacent hd _ ih => exact .adjacent hd ih
  | separated hd _ ih => exact .adjacent hd ih

theorem Hexadecimal.erasure {raw : Bytes} {n : NumLit} (h : Hexadecimal raw n) :
    Hexadecimal (eraseUnderscores raw) n := by
  cases h with
  | mk hd =>
    change Hexadecimal (48 :: 120 :: eraseUnderscores _) _
    rw [hd.erasure]
    exact .mk hd.canonical

theorem hexNumber_erasure {raw : Bytes} {n : NumLit} (h : hexNumber raw = some n) :
    hexNumber (eraseUnderscores raw) = some n :=
  (Hexadecimal.complete h).erasure.sound

theorem hexVal_lt16 {b : UInt8} (hd : isHexDigit b = true) : hexVal b < 16 := by
  simp only [isHexDigit, isDigit, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  dsimp only [hexVal]
  split
  · omega
  · split <;> omega

theorem toFin16_value {b : UInt8} (hd : isHexDigit b = true) :
    (toFin16 b).val = hexVal b := Nat.mod_eq_of_lt (hexVal_lt16 hd)

theorem HexDigits.all_digits {raw ds : Bytes} (h : HexDigits raw ds) :
    ds.all isHexDigit = true := by
  induction h with
  | single hd => exact Bool.and_eq_true_iff.mpr ⟨hd, rfl⟩
  | adjacent hd _ ih => exact Bool.and_eq_true_iff.mpr ⟨hd, ih⟩
  | separated hd _ ih => exact Bool.and_eq_true_iff.mpr ⟨hd, ih⟩

/-- Fin conversion agrees with the independent raw-byte base-16 fold. -/
theorem hex_fold (ds : Bytes) (hd : ds.all isHexDigit = true) (a : Int) :
    (ds.map toFin16).foldl (fun acc d => acc * 16 + (d.val : Int)) a =
      ds.foldl (fun acc b => acc * 16 + (hexVal b : Int)) a := by
  induction ds generalizing a with
  | nil => rfl
  | cons b ds ih =>
    have hc := Bool.and_eq_true_iff.mp hd
    simp only [List.map_cons, List.foldl_cons, toFin16_value hc.1]
    exact ih hc.2 _

/-- An accepted hexadecimal's value is the exact raw-byte fold, and its flag
is precisely the existing deterministic eip55 computation on decoded digits. -/
theorem hexadecimal_decode_value {raw : Bytes} {n : NumLit}
    (h : hexNumber raw = some n) :
    ∃ spelling ds : Bytes,
      raw = 48 :: 120 :: spelling ∧ HexDigits spelling ds ∧
      n = .hex (ds.map toFin16) (eip55 ds) ∧
      n.value = Q.ofInt (ds.foldl (fun acc b => acc * 16 + (hexVal b : Int)) 0) := by
  cases Hexadecimal.complete h with
  | @mk spelling ds hd =>
    refine ⟨spelling, ds, rfl, hd, rfl, ?_⟩
    simp only [NumLit.value]
    rw [hex_fold ds hd.all_digits 0]

/-- Accepted decimal interpretation, retaining integer/fraction/exponent
components and the exact numerator and denominator of Source's Q. -/
theorem decimal_decode_value {raw : Bytes} {n : NumLit}
    (h : decNumber raw = some n) :
    ∃ ip r1 fp r2 : Bytes, ∃ e : Int,
      IntegerPart raw ip r1 ∧ FractionPart r1 fp r2 ∧ Exponent r2 e ∧
      n = .dec (digitsVal (ip ++ fp)) fp.length e ∧
      n.value = if 0 ≤ e then
        ⟨digitsVal (ip ++ fp) * 10 ^ e.toNat, 10 ^ fp.length, Nat.pow_pos (by decide)⟩
      else ⟨digitsVal (ip ++ fp), 10 ^ (fp.length + e.natAbs), Nat.pow_pos (by decide)⟩ := by
  cases Decimal.complete h with
  | @mk ip r1 fp r2 e hi hf _ _ he =>
    exact ⟨ip, r1, fp, r2, e, hi, hf, he, rfl, rfl⟩

/-- Exact decimal fold at an arbitrary initial accumulator. No digit-class
restriction is needed for this arithmetic identity. -/
theorem decimal_fold (ds : Bytes) (a : Nat) :
    ds.foldl (fun acc b => 10 * acc + (b.toNat - 48)) a =
      10 ^ ds.length * a + digitsVal ds := by
  induction ds generalizing a with
  | nil =>
    change a = 10 ^ 0 * a + 0
    simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | cons b ds ih =>
    change ds.foldl (fun acc b => 10 * acc + (b.toNat - 48))
      (10 * a + (b.toNat - 48)) = 10 ^ (ds.length + 1) * a + digitsVal (b :: ds)
    rw [ih]
    have hb : digitsVal (b :: ds) = 10 ^ ds.length * (b.toNat - 48) + digitsVal ds := by
      unfold digitsVal
      simp only [List.foldl_cons, Nat.mul_zero, Nat.zero_add]
      exact ih _
    rw [hb, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem digitsVal_append (ip fp : Bytes) :
    digitsVal (ip ++ fp) = 10 ^ fp.length * digitsVal ip + digitsVal fp := by
  unfold digitsVal
  rw [List.foldl_append]
  exact decimal_fold fp _

/-- The mantissa is integer-part times scale plus fractional digits, before
Source's signed decimal exponent is applied. -/
theorem decimal_decode_mantissa {raw : Bytes} {n : NumLit}
    (h : decNumber raw = some n) :
    ∃ ip r1 fp r2 : Bytes, ∃ e : Int,
      IntegerPart raw ip r1 ∧ FractionPart r1 fp r2 ∧ Exponent r2 e ∧
      n = .dec (10 ^ fp.length * digitsVal ip + digitsVal fp) fp.length e := by
  cases Decimal.complete h with
  | @mk ip r1 fp r2 e hi hf _ _ he =>
    refine ⟨ip, r1, fp, r2, e, hi, hf, he, ?_⟩
    rw [digitsVal_append]

end Solidity.Frontend.NumericLiteralProofs
