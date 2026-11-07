import Solidity.Frontend.Checked.Lexer

/-!
# Independent decimal digit spelling

`Tail` describes maximal decimal-tail scanning, including a leading underscore
followed by a digit. `Digits` requires the initial digit. Neither relation uses
the scanner to define correctness. Every stop preserves the entire suffix.
-/
namespace Solidity.Frontend.NumericLiteralProofs

open Solidity.Frontend.Checked

inductive Tail : Bytes → Bytes → Bytes → Prop where
  | nil : Tail [] [] []
  | digit {b : UInt8} {r ds rest : Bytes} (hd : isDigit b = true)
      (tail : Tail r ds rest) : Tail (b :: r) (b :: ds) rest
  | separated {b c : UInt8} {r ds rest : Bytes}
      (hd : isDigit b = false) (hu : (b.toNat == 95) = true)
      (hc : isDigit c = true) (tail : Tail r ds rest) :
      Tail (b :: c :: r) (c :: ds) rest
  | other {b : UInt8} {r : Bytes} (hd : isDigit b = false)
      (hu : (b.toNat == 95) = false) : Tail (b :: r) [] (b :: r)
  | finalUnderscore {b : UInt8} (hd : isDigit b = false)
      (hu : (b.toNat == 95) = true) : Tail [b] [] [b]
  | badUnderscore {b c : UInt8} {r : Bytes} (hd : isDigit b = false)
      (hu : (b.toNat == 95) = true) (hc : isDigit c = false) :
      Tail (b :: c :: r) [] (b :: c :: r)

inductive Digits : Bytes → Bytes → Bytes → Prop where
  | first {b : UInt8} {r ds rest : Bytes} (hd : isDigit b = true)
      (tail : Tail r ds rest) : Digits (b :: r) (b :: ds) rest

/-- Every independently derived tail has exactly the scanner's output. -/
theorem Tail.sound {raw ds rest : Bytes} (h : Tail raw ds rest) :
    digitsTail raw = (ds, rest) := by
  induction h with
  | nil => rfl
  | digit hd _ ih => unfold digitsTail; simp only [hd, ↓reduceIte, ih]
  | separated hd hu hc _ ih =>
    simp only [digitsTail, hd, Bool.false_eq_true, ↓reduceIte, hu, hc, ih]
  | other hd hu =>
    unfold digitsTail; simp only [hd, Bool.false_eq_true, ↓reduceIte, hu]
  | finalUnderscore hd hu =>
    simp only [digitsTail, hd, Bool.false_eq_true, ↓reduceIte, hu]
  | badUnderscore hd hu hc =>
    simp only [digitsTail, hd, Bool.false_eq_true, ↓reduceIte, hu, hc]

/-- Every input has the independent derivation matching the computed output. -/
theorem Tail.complete (raw : Bytes) :
    Tail raw (digitsTail raw).1 (digitsTail raw).2 := by
  cases raw with
  | nil => exact .nil
  | cons b r =>
    by_cases hd : isDigit b = true
    · unfold digitsTail
      simp only [hd, ↓reduceIte]
      exact .digit hd (Tail.complete r)
    · have hf : isDigit b = false := Bool.eq_false_iff.mpr hd
      by_cases hu : (b.toNat == 95) = true
      · cases r with
        | nil =>
          unfold digitsTail
          simp only [hf, Bool.false_eq_true, ↓reduceIte, hu]
          exact .finalUnderscore hf hu
        | cons c t =>
          by_cases hc : isDigit c = true
          · unfold digitsTail
            simp only [hf, Bool.false_eq_true, ↓reduceIte, hu, hc]
            exact .separated hf hu hc (Tail.complete t)
          · have hcf : isDigit c = false := Bool.eq_false_iff.mpr hc
            unfold digitsTail
            simp only [hf, Bool.false_eq_true, ↓reduceIte, hu, hcf]
            exact .badUnderscore hf hu hcf
      · have huf : (b.toNat == 95) = false := Bool.eq_false_iff.mpr hu
        unfold digitsTail
        simp only [hf, Bool.false_eq_true, ↓reduceIte, huf]
        exact .other hf huf
termination_by raw.length

/-- Universal agreement, including all retained suffixes. -/
theorem tail_iff {raw ds rest : Bytes} :
    Tail raw ds rest ↔ digitsTail raw = (ds, rest) := by
  constructor
  · exact Tail.sound
  · intro h
    have hc : Tail raw (digitsTail raw).1 (digitsTail raw).2 := Tail.complete raw
    rw [h] at hc
    exact hc

theorem Digits.sound {raw ds rest : Bytes} (h : Digits raw ds rest) :
    digits1 raw = some (ds, rest) := by
  cases h with
  | first hd ht =>
    simp only [digits1, hd, ↓reduceIte, ht.sound]

theorem Digits.complete {raw ds rest : Bytes}
    (h : digits1 raw = some (ds, rest)) : Digits raw ds rest := by
  cases raw with
  | nil => simp only [digits1, reduceCtorEq] at h
  | cons b r =>
    by_cases hd : isDigit b = true
    · simp only [digits1, hd, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨hds, hrest⟩
      rw [← hds, ← hrest]
      exact .first hd (Tail.complete r)
    · simp only [digits1, hd, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

theorem digits_iff {raw ds rest : Bytes} :
    Digits raw ds rest ↔ digits1 raw = some (ds, rest) :=
  ⟨Digits.sound, Digits.complete⟩

/-- Erase underscore bytes, retaining every other byte. -/
def eraseUnderscores (raw : Bytes) : Bytes := raw.filter (fun b => b.toNat != 95)

theorem digit_not_underscore {b : UInt8} (hd : isDigit b = true) :
    (b.toNat != 95) = true := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  simp only [bne_iff_ne, ne_eq]
  omega

/-- Exact consumed prefix and underscore erasure, with arbitrary leftover. -/
theorem Tail.consumed {raw ds rest : Bytes} (h : Tail raw ds rest) :
    ∃ pre : Bytes, raw = pre ++ rest ∧ eraseUnderscores pre = ds := by
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @digit b r ds rest hd ht ih =>
    obtain ⟨pre, hr, he⟩ := ih
    refine ⟨b :: pre, ?_, ?_⟩
    · rw [hr]; rfl
    · simp only [eraseUnderscores, List.filter_cons, digit_not_underscore hd,
        ↓reduceIte, ← he]
  | @separated b c r ds rest hd hu hc ht ih =>
    obtain ⟨pre, hr, he⟩ := ih
    refine ⟨b :: c :: pre, ?_, ?_⟩
    · rw [hr]; rfl
    · have hb : (b.toNat != 95) = false := by
        change (!(b.toNat == 95)) = false
        rw [hu]; rfl
      simp only [eraseUnderscores, List.filter_cons, hb, Bool.false_eq_true,
        ↓reduceIte, digit_not_underscore hc, ← he]
  | other _ _ => exact ⟨[], rfl, rfl⟩
  | finalUnderscore _ _ => exact ⟨[], rfl, rfl⟩
  | badUnderscore _ _ _ => exact ⟨[], rfl, rfl⟩

theorem Digits.consumed {raw ds rest : Bytes} (h : Digits raw ds rest) :
    ∃ pre : Bytes, raw = pre ++ rest ∧ eraseUnderscores pre = ds ∧ pre ≠ [] := by
  cases h with
  | @first b r tailDigits rest hd ht =>
    obtain ⟨pre, hr, he⟩ := ht.consumed
    refine ⟨b :: pre, ?_, ?_, List.cons_ne_nil _ _⟩
    · rw [hr]; rfl
    · simp only [eraseUnderscores, List.filter_cons, digit_not_underscore hd,
        ↓reduceIte, ← he]

theorem Tail.all_digits {raw ds rest : Bytes} (h : Tail raw ds rest) :
    ds.all isDigit = true := by
  induction h with
  | nil => rfl
  | digit hd _ ih => exact Bool.and_eq_true_iff.mpr ⟨hd, ih⟩
  | separated _ _ hc _ ih => exact Bool.and_eq_true_iff.mpr ⟨hc, ih⟩
  | other _ _ => rfl
  | finalUnderscore _ _ => rfl
  | badUnderscore _ _ _ => rfl

theorem Digits.all_digits {raw ds rest : Bytes} (h : Digits raw ds rest) :
    ds.all isDigit = true := by
  cases h with
  | first hd ht => exact Bool.and_eq_true_iff.mpr ⟨hd, ht.all_digits⟩

/-- No nonempty digit spelling can decode to an empty digit list. -/
theorem Digits.nonempty {raw ds rest : Bytes} (h : Digits raw ds rest) : ds ≠ [] := by
  cases h
  exact List.cons_ne_nil _ _

/-- Digit-value preservation for the exact consumed spelling. -/
theorem Digits.value_erasure {raw ds rest : Bytes} (h : Digits raw ds rest) :
    ∃ pre : Bytes, raw = pre ++ rest ∧
      digitsVal (eraseUnderscores pre) = digitsVal ds := by
  obtain ⟨pre, hr, he, _⟩ := h.consumed
  exact ⟨pre, hr, congrArg digitsVal he⟩

/-- A canonical digit list can precede any independently stopped suffix. -/
theorem Tail.canonical {ds rest : Bytes} (hd : ds.all isDigit = true)
    (hs : Tail rest [] rest) : Tail (ds ++ rest) ds rest := by
  induction ds with
  | nil => exact hs
  | cons b ds ih =>
    have hc := Bool.and_eq_true_iff.mp hd
    exact .digit hc.1 (ih hc.2)

theorem Digits.canonical {ds rest : Bytes} (hd : ds.all isDigit = true)
    (hn : ds ≠ []) (hs : Tail rest [] rest) : Digits (ds ++ rest) ds rest := by
  cases ds with
  | nil => exact False.elim (hn rfl)
  | cons b ds =>
    have hc := Bool.and_eq_true_iff.mp hd
    exact .first hc.1 (Tail.canonical hc.2 hs)

/-- Erasing underscores is valid when the erased delimiter remains a stop.
The hypothesis is necessary for arbitrary suffixes such as doubled underscores;
whole numeric spelling theorems discharge it from the delimiter grammar. -/
theorem Digits.erasure {raw ds rest : Bytes} (h : Digits raw ds rest)
    (hs : Tail (eraseUnderscores rest) [] (eraseUnderscores rest)) :
    Digits (eraseUnderscores raw) ds (eraseUnderscores rest) := by
  obtain ⟨pre, hr, he, _⟩ := h.consumed
  have her : eraseUnderscores raw = ds ++ eraseUnderscores rest := by
    rw [hr]
    change (pre ++ rest).filter _ = _
    rw [List.filter_append]
    rw [← he]
    rfl
  rw [her]
  exact Digits.canonical h.all_digits h.nonempty hs

/-- Extend a fully consumed spelling by an independently stopped suffix. -/
theorem Tail.append_stop {raw ds rest suffix : Bytes} (h : Tail raw ds rest)
    (hr : rest = []) (hs : Tail suffix [] suffix) :
    Tail (raw ++ suffix) ds suffix := by
  induction h with
  | nil => exact hs
  | digit hd _ ih => exact .digit hd (ih hr)
  | separated hd hu hc _ ih => exact .separated hd hu hc (ih hr)
  | other _ _ => cases hr
  | finalUnderscore _ _ => cases hr
  | badUnderscore _ _ _ => cases hr

theorem Digits.append_stop {raw ds rest suffix : Bytes} (h : Digits raw ds rest)
    (hr : rest = []) (hs : Tail suffix [] suffix) :
    Digits (raw ++ suffix) ds suffix := by
  cases h with
  | first hd ht => exact .first hd (ht.append_stop hr hs)

end Solidity.Frontend.NumericLiteralProofs
