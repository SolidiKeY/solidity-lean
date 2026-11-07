import Solidity.Frontend.NumericLiteralProofs.Digits
import Solidity.Source.Const

/-!
# Independent decimal and hexadecimal numeric spelling

The relations preserve decoded digits, fractional scale, signed exponent and the
existing deterministic checksum flag. Constructors use byte classes and digit
relations, never `decNumber` or `hexNumber` to define correctness.
-/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

inductive NoDigits : Bytes → Prop where
  | nil : NoDigits []
  | other {b : UInt8} {r : Bytes} (hd : isDigit b = false) : NoDigits (b :: r)

inductive IntegerPart : Bytes → Bytes → Bytes → Prop where
  | absent {raw : Bytes} (h : NoDigits raw) : IntegerPart raw [] raw
  | present {raw ds rest : Bytes} (h : Digits raw ds rest) : IntegerPart raw ds rest

inductive FractionPart : Bytes → Bytes → Bytes → Prop where
  | nil : FractionPart [] [] []
  | absent {b : UInt8} {r : Bytes} (hd : b ≠ 46) : FractionPart (b :: r) [] (b :: r)
  | present {raw ds rest : Bytes} (h : Digits raw ds rest) :
      FractionPart (46 :: raw) ds rest

inductive Exponent : Bytes → Int → Prop where
  | absent : Exponent [] 0
  | unsigned {e : UInt8} {raw ds : Bytes} (he : e.toNat = 101 ∨ e.toNat = 69)
      (h : Digits raw ds []) : Exponent (e :: raw) (digitsVal ds : Int)
  | negative {e : UInt8} {raw ds : Bytes} (he : e.toNat = 101 ∨ e.toNat = 69)
      (h : Digits raw ds []) : Exponent (e :: 45 :: raw) (-(digitsVal ds : Int))

inductive Decimal : Bytes → NumLit → Prop where
  | mk {raw ip r1 fp r2 : Bytes} {e : Int}
      (integer : IntegerPart raw ip r1) (fraction : FractionPart r1 fp r2)
      (nonempty : ip ≠ [] ∨ fp ≠ [])
      (notOctal : ¬(ip.length > 1 ∧ ip.head? = some 48))
      (exponent : Exponent r2 e) :
      Decimal raw (.dec (digitsVal (ip ++ fp)) fp.length e)

inductive HexDigits : Bytes → Bytes → Prop where
  | single {b : UInt8} (hd : isHexDigit b = true) : HexDigits [b] [b]
  | adjacent {b : UInt8} {raw ds : Bytes} (hd : isHexDigit b = true)
      (tail : HexDigits raw ds) : HexDigits (b :: raw) (b :: ds)
  | separated {b : UInt8} {raw ds : Bytes} (hd : isHexDigit b = true)
      (tail : HexDigits raw ds) : HexDigits (b :: 95 :: raw) (b :: ds)

inductive Hexadecimal : Bytes → NumLit → Prop where
  | mk {raw ds : Bytes} (digits : HexDigits raw ds) :
      Hexadecimal (48 :: 120 :: raw) (.hex (ds.map toFin16) (eip55 ds))

theorem hex_digit_not_underscore {b : UInt8} (hd : isHexDigit b = true) : b ≠ 95 := by
  simp only [isHexDigit, isDigit, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  intro hb
  subst b
  contradiction

theorem HexDigits.nonempty {raw ds : Bytes} (h : HexDigits raw ds) : raw ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem HexDigits.head {b : UInt8} {r ds : Bytes} (h : HexDigits (b :: r) ds) :
    isHexDigit b = true := by
  cases h with
  | single hd => exact hd
  | adjacent hd _ => exact hd
  | separated hd _ => exact hd

theorem HexDigits.sound {raw ds : Bytes} (h : HexDigits raw ds) :
    hexDigits raw = some ds := by
  induction h with
  | single hd => simp only [hexDigits, hd, ↓reduceIte]
  | @adjacent b raw ds hd ht ih =>
    cases raw with
    | nil => exact False.elim (ht.nonempty rfl)
    | cons c r =>
      have hc : c ≠ 95 := hex_digit_not_underscore ht.head
      unfold hexDigits
      split
      · next _ _ he =>
          simp only [List.cons.injEq, List.cons_ne_nil, and_false] at he
      · next _ _ _ he =>
          simp only [List.cons.injEq] at he
          exact False.elim (hc he.2.1)
      · next _ _ _ _ _ he =>
          simp only [List.cons.injEq] at he
          rcases he with ⟨rfl, hr⟩
          rw [← hr]
          simp only [hd, ↓reduceIte, ih, Option.map_some]
      · next _ he => cases he
  | @separated b raw ds hd ht ih =>
    cases raw with
    | nil => exact False.elim (ht.nonempty rfl)
    | cons c r =>
      simp only [hexDigits, hd, List.isEmpty_cons, Bool.not_false,
        Bool.and_self, ↓reduceIte, ih, Option.map_some]

theorem HexDigits.complete (raw : Bytes) :
    ∀ ds : Bytes, hexDigits raw = some ds → HexDigits raw ds := by
  fun_induction hexDigits raw <;> intro ds h
  all_goals try simp only [Bool.and_eq_true] at *
  all_goals simp only [Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] at h
  all_goals first
    | contradiction
    | exact h ▸ HexDigits.single (by assumption)
    | obtain ⟨out, hout, rfl⟩ := h
      first
        | exact HexDigits.separated (And.left (by assumption)) (by solve_by_elim)
        | exact HexDigits.adjacent (by assumption) (by solve_by_elim)

theorem hex_digits_iff {raw ds : Bytes} :
    HexDigits raw ds ↔ hexDigits raw = some ds :=
  ⟨HexDigits.sound, HexDigits.complete raw ds⟩

theorem Hexadecimal.sound {raw : Bytes} {n : NumLit} (h : Hexadecimal raw n) :
    hexNumber raw = some n := by
  cases h with
  | mk hd => simp only [hexNumber, hd.sound, Option.map_some]

theorem Hexadecimal.complete {raw : Bytes} {n : NumLit}
    (h : hexNumber raw = some n) : Hexadecimal raw n := by
  unfold hexNumber at h
  split at h
  · next _ r =>
      obtain ⟨ds, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .mk (HexDigits.complete r ds hd)
  · contradiction

theorem hexadecimal_iff {raw : Bytes} {n : NumLit} :
    Hexadecimal raw n ↔ hexNumber raw = some n :=
  ⟨Hexadecimal.sound, Hexadecimal.complete⟩

theorem HexDigits.erasure {raw ds : Bytes} (h : HexDigits raw ds) :
    eraseUnderscores raw = ds := by
  have keep {b : UInt8} (hd : isHexDigit b = true) : (b.toNat != 95) = true := by
    simp only [isHexDigit, isDigit, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hd
    simp only [bne_iff_ne, ne_eq]
    omega
  induction h with
  | single hd =>
      simp only [eraseUnderscores, List.filter_cons, List.filter_nil, keep hd, ↓reduceIte]
  | adjacent hd ht ih =>
      simp only [eraseUnderscores, List.filter_cons, keep hd, ↓reduceIte, ← ih]
  | separated hd ht ih =>
      simp only [eraseUnderscores, List.filter_cons, keep hd, ↓reduceIte, ← ih]
      rfl

/-- Hex spelling preserves the exact digit-value fold after underscore erasure. -/
theorem HexDigits.value_erasure {raw ds : Bytes} (h : HexDigits raw ds) :
    ((eraseUnderscores raw).map toFin16).foldl (fun a d => a * 16 + d.val) 0 =
      (ds.map toFin16).foldl (fun a d => a * 16 + d.val) 0 := by
  rw [h.erasure]

theorem NoDigits.sound {raw : Bytes} (h : NoDigits raw) : digits1 raw = none := by
  cases h with
  | nil => rfl
  | other hd => simp only [digits1, hd, Bool.false_eq_true, ↓reduceIte]

theorem NoDigits.complete {raw : Bytes} (h : digits1 raw = none) : NoDigits raw := by
  cases raw with
  | nil => exact .nil
  | cons b r =>
    by_cases hd : isDigit b = true
    · simp only [digits1, hd, ↓reduceIte, reduceCtorEq] at h
    · exact .other (Bool.eq_false_iff.mpr hd)

theorem IntegerPart.sound {raw ds rest : Bytes} (h : IntegerPart raw ds rest) :
    (match digits1 raw with | some p => p | none => ([], raw)) = (ds, rest) := by
  cases h with
  | absent hn => simp only [hn.sound]
  | present hd => simp only [hd.sound]

theorem IntegerPart.complete (raw : Bytes) :
    ∃ ds rest : Bytes, IntegerPart raw ds rest := by
  cases h : digits1 raw with
  | none => exact ⟨[], raw, .absent (NoDigits.complete h)⟩
  | some p => exact ⟨p.1, p.2, .present (Digits.complete h)⟩

/-- Auxiliary computation used only in correspondence proofs, not in the grammar. -/
def readFraction : Bytes → Option (Bytes × Bytes)
  | 46 :: r => digits1 r
  | r => some ([], r)

theorem FractionPart.sound {raw ds rest : Bytes} (h : FractionPart raw ds rest) :
    readFraction raw = some (ds, rest) := by
  cases h with
  | nil => rfl
  | @absent b r hb =>
    unfold readFraction
    split
    · next r he =>
        simp only [List.cons.injEq] at he
        exact False.elim (hb he.1)
    · rfl
  | present hd => exact hd.sound

def readExponent : Bytes → Option Int
  | [] => some 0
  | e :: r =>
    if e.toNat == 101 || e.toNat == 69 then
      match r with
      | 45 :: r' => match digits1 r' with
        | some (ds, []) => some (-(digitsVal ds : Int))
        | _ => none
      | r' => match digits1 r' with
        | some (ds, []) => some (digitsVal ds : Int)
        | _ => none
    else none

theorem Exponent.sound {raw : Bytes} {e : Int} (h : Exponent raw e) :
    readExponent raw = some e := by
  cases h with
  | absent => rfl
  | @unsigned e raw ds he hd =>
    have he' : (e.toNat == 101 || e.toNat == 69) = true := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using he
    have hr : raw ≠ [] := by
      intro hn
      subst raw
      cases hd
    cases raw with
    | nil => contradiction
    | cons b r =>
      have hb : b ≠ 45 := by
        have hdb : isDigit b = true := by cases hd; assumption
        intro h45
        subst b
        contradiction
      unfold readExponent
      simp only [he', ↓reduceIte]
      split
      · next r heq =>
          simp only [List.cons.injEq] at heq
          exact False.elim (hb heq.1)
      · simp only [hd.sound]
  | @negative e raw ds he hd =>
    have he' : (e.toNat == 101 || e.toNat == 69) = true := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using he
    simp only [readExponent, he', ↓reduceIte, hd.sound]

theorem FractionPart.complete {raw ds rest : Bytes}
    (h : readFraction raw = some (ds, rest)) : FractionPart raw ds rest := by
  unfold readFraction at h
  split at h
  · next _ r => exact .present (Digits.complete h)
  · next _ hn =>
      cases h
      cases raw with
      | nil => exact .nil
      | cons b r =>
          apply FractionPart.absent
          intro hb
          subst b
          exact hn r rfl

theorem Exponent.complete {raw : Bytes} {e : Int}
    (h : readExponent raw = some e) : Exponent raw e := by
  unfold readExponent at h
  split at h
  · cases h; exact .absent
  · next _ b r =>
      split at h
      · next he =>
          have he' : b.toNat = 101 ∨ b.toNat = 69 := by
            simpa only [Bool.or_eq_true, beq_iff_eq] using he
          split at h
          · next r =>
              split at h
              · next ds hds =>
                  cases h
                  exact .negative he' (Digits.complete hds)
              · contradiction
          · next r hn =>
              split at h
              · next ds hds =>
                  cases h
                  exact .unsigned he' (Digits.complete hds)
              · contradiction
      · contradiction

theorem decNumber_parts {raw ip r1 : Bytes} (hi : IntegerPart raw ip r1) :
    decNumber raw =
      match readFraction r1 with
      | none => none
      | some (fp, r2) =>
        if ip.isEmpty && fp.isEmpty then none
        else if ip.length > 1 && ip.head? == some 48 then none
        else (readExponent r2).map (fun x => .dec (digitsVal (ip ++ fp)) fp.length x) := by
  cases hi with
  | absent h => unfold decNumber; rw [h.sound]; rfl
  | present h => unfold decNumber; rw [h.sound]; rfl

theorem Decimal.sound {raw : Bytes} {n : NumLit} (h : Decimal raw n) :
    decNumber raw = some n := by
  cases h with
  | @mk ip r1 fp r2 e hi hf hn ho he =>
    have hn' : (ip.isEmpty && fp.isEmpty) = false := by
      apply Bool.eq_false_iff.mpr
      intro hboth
      have hb := Bool.and_eq_true_iff.mp hboth
      simp only [List.isEmpty_iff] at hb
      rcases hn with hp | hp
      · exact hp hb.1
      · exact hp hb.2
    have ho' : (ip.length > 1 && ip.head? == some 48) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      have hb' := Bool.and_eq_true_iff.mp hb
      exact ho ⟨of_decide_eq_true hb'.1, beq_iff_eq.mp hb'.2⟩
    rw [decNumber_parts hi, hf.sound]
    simp only [hn', ho', Bool.false_eq_true, ↓reduceIte, he.sound, Option.map_some]

theorem Decimal.complete {raw : Bytes} {n : NumLit}
    (h : decNumber raw = some n) : Decimal raw n := by
  obtain ⟨ip, r1, hi⟩ := IntegerPart.complete raw
  rw [decNumber_parts hi] at h
  cases hf : readFraction r1 with
  | none => simp only [hf, reduceCtorEq] at h
  | some pair =>
    obtain ⟨fp, r2⟩ := pair
    rw [hf] at h
    by_cases hn : (ip.isEmpty && fp.isEmpty) = true
    · simp only [hn, ↓reduceIte, reduceCtorEq] at h
    · by_cases ho : (ip.length > 1 && ip.head? == some 48) = true
      · simp only [hn, ho, ↓reduceIte, reduceCtorEq] at h
      · simp only [hn, ho] at h
        obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
        have hne : ip ≠ [] ∨ fp ≠ [] := by
          by_cases hip : ip = []
          · right
            intro hfp
            subst ip; subst fp
            exact hn rfl
          · exact Or.inl hip
        have hno : ¬(ip.length > 1 ∧ ip.head? = some 48) := by
          intro hc
          exact ho (Bool.and_eq_true_iff.mpr
            ⟨decide_eq_true_eq.mpr hc.1, beq_iff_eq.mpr hc.2⟩)
        exact .mk hi (FractionPart.complete hf) hne hno (Exponent.complete he)

theorem decimal_iff {raw : Bytes} {n : NumLit} :
    Decimal raw n ↔ decNumber raw = some n :=
  ⟨Decimal.sound, Decimal.complete⟩

/-- The semantic decimal scale/exponent, in the existing unnormalised Q. -/
theorem decimal_value (m f : Nat) (e : Int) :
    (NumLit.dec m f e).value =
      if _h : 0 ≤ e then
        ⟨m * 10 ^ e.toNat, 10 ^ f, Nat.pow_pos (by decide)⟩
      else ⟨m, 10 ^ (f + e.natAbs), Nat.pow_pos (by decide)⟩ := rfl

/-- Hexadecimal interpretation is the exact base-16 fold; the flag is irrelevant. -/
theorem hexadecimal_value (ds : List (Fin 16)) (flag : Bool) :
    (NumLit.hex ds flag).value =
      Q.ofInt (ds.foldl (fun acc d => acc * 16 + d.val) 0) := rfl

end Solidity.Frontend.NumericLiteralProofs
