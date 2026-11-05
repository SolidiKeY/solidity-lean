import Solidity.Frontend.NumericLiteralProofs.Backfill

/-! # Source-level glued numeric suffix refusal -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem split_glued_48 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (48 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (48 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (48 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_49 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (49 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (49 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (49 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_50 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (50 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (50 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (50 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_51 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (51 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (51 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (51 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_52 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (52 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (52 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (52 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_53 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (53 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (53 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (53 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_54 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (54 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (54 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (54 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_55 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (55 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (55 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (55 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_56 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (56 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (56 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (56 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_57 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (57 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (57 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (57 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_digit (b c : UInt8) (r digits suffix : Bytes)
    (hd : isDigit b = true)
    (hs : numberSpan false (b :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (b :: r) = .error "number followed by an identifier character" := by
  have hn := hd
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hn
  have hb : b.toNat = 48 ∨ b.toNat = 49 ∨ b.toNat = 50 ∨ b.toNat = 51 ∨ b.toNat = 52 ∨ b.toNat = 53 ∨ b.toNat = 54 ∨ b.toNat = 55 ∨ b.toNat = 56 ∨ b.toNat = 57 := by omega
  rcases hb with h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57
  · have he : b = 48 := UInt8.toNat_inj.mp h48
    subst b
    exact split_glued_48 r digits suffix c hs hc
  · have he : b = 49 := UInt8.toNat_inj.mp h49
    subst b
    exact split_glued_49 r digits suffix c hs hc
  · have he : b = 50 := UInt8.toNat_inj.mp h50
    subst b
    exact split_glued_50 r digits suffix c hs hc
  · have he : b = 51 := UInt8.toNat_inj.mp h51
    subst b
    exact split_glued_51 r digits suffix c hs hc
  · have he : b = 52 := UInt8.toNat_inj.mp h52
    subst b
    exact split_glued_52 r digits suffix c hs hc
  · have he : b = 53 := UInt8.toNat_inj.mp h53
    subst b
    exact split_glued_53 r digits suffix c hs hc
  · have he : b = 54 := UInt8.toNat_inj.mp h54
    subst b
    exact split_glued_54 r digits suffix c hs hc
  · have he : b = 55 := UInt8.toNat_inj.mp h55
    subst b
    exact split_glued_55 r digits suffix c hs hc
  · have he : b = 56 := UInt8.toNat_inj.mp h56
    subst b
    exact split_glued_56 r digits suffix c hs hc
  · have he : b = 57 := UInt8.toNat_inj.mp h57
    subst b
    exact split_glued_57 r digits suffix c hs hc

theorem lex_glued_digit (b c : UInt8) (r digits suffix : Bytes)
    (hd : isDigit b = true)
    (hs : numberSpan false (b :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    lex (b :: r) = .error ⟨0, "number followed by an identifier character"⟩ := by
  have hg := split_glued_digit b c r digits suffix hd hs hc
  unfold lex
  rw [scan, hg]
  simp only [Nat.sub_self]
  all_goals exact List.cons_ne_nil _ _

theorem takeWhile_reprint (p : UInt8 → Bool) (raw : Bytes) :
    raw.takeWhile p ++ raw.drop (raw.takeWhile p).length = raw := by
  induction raw with
  | nil => rfl
  | cons b r ih =>
    by_cases hb : p b = true
    · simp only [List.takeWhile_cons, hb, ↓reduceIte, List.length_cons,
        List.drop_succ_cons, List.cons_append, ih]
    · simp only [List.takeWhile_cons, hb, Bool.false_eq_true, ↓reduceIte, List.length_nil,
        List.drop_zero, List.nil_append]

def fractionalSpan (raw : Bytes) : Bytes :=
  match raw with
  | 46 :: d :: _ => if isDigit d then
      46 :: (raw.drop 1).takeWhile (fun b => isDigit b || b.toNat == 95) else []
  | _ => []

def exponentialSpan (raw : Bytes) : Bytes :=
  match raw with
  | e :: 45 :: d :: _ =>
      if (e.toNat == 101 || e.toNat == 69) && isDigit d then
        e :: 45 :: (raw.drop 2).takeWhile (fun b => isDigit b || b.toNat == 95) else []
  | e :: d :: _ =>
      if (e.toNat == 101 || e.toNat == 69) && isDigit d then
        e :: (raw.drop 1).takeWhile (fun b => isDigit b || b.toNat == 95) else []
  | _ => []

theorem fractionalSpan_reprint (raw : Bytes) :
    fractionalSpan raw ++ raw.drop (fractionalSpan raw).length = raw := by
  unfold fractionalSpan
  split
  · next d r =>
    split
    · simp only [List.length_cons, List.drop_succ_cons, List.drop_zero, List.cons_append]
      rw [takeWhile_reprint]
    · rfl
  · rfl

theorem exponentialSpan_reprint (raw : Bytes) :
    exponentialSpan raw ++ raw.drop (exponentialSpan raw).length = raw := by
  unfold exponentialSpan
  split
  · split
    · simp only [List.length_cons, List.drop_succ_cons, List.drop_zero, List.cons_append]
      rw [takeWhile_reprint]
    · rfl
  · split
    · simp only [List.length_cons, List.drop_succ_cons, List.drop_zero, List.cons_append]
      rw [takeWhile_reprint]
    · rfl
  · rfl

/-- Exact numeric-span consumption, for all bytes and in both numeric modes,
including malformed spellings which classification later refuses. -/
theorem numberSpan_reprint (yul : Bool) (raw : Bytes) :
    (numberSpan yul raw).1 ++ (numberSpan yul raw).2 = raw := by
  unfold numberSpan
  split
  · simp only [List.cons_append]
    rw [takeWhile_reprint]
  · by_cases hy : yul = true
    · simp only [hy, ↓reduceIte]
      exact takeWhile_reprint _ _
    · have hyf : yul = false := Bool.eq_false_iff.mpr hy
      simp only [hyf, Bool.false_eq_true, ↓reduceIte]
      let ip := raw.takeWhile (fun b => isDigit b || (!false && b.toNat == 95))
      let r1 := raw.drop ip.length
      let fp := fractionalSpan r1
      let r2 := r1.drop fp.length
      let ep := exponentialSpan r2
      change (ip ++ fp ++ ep) ++ r2.drop ep.length = raw
      rw [List.append_assoc, List.append_assoc, exponentialSpan_reprint,
        fractionalSpan_reprint, takeWhile_reprint]

theorem split_glued_dot_48 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 48 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 48 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 48 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_49 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 49 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 49 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 49 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_50 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 50 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 50 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 50 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_51 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 51 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 51 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 51 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_52 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 52 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 52 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 52 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_53 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 53 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 53 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 53 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_54 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 54 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 54 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 54 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_55 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 55 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 55 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 55 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_56 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 56 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 56 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 56 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot_57 (r digits suffix : Bytes) (c : UInt8)
    (hs : numberSpan false (46 :: 57 :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: 57 :: r) = .error "number followed by an identifier character" := by
  change (let p := numberSpan false (46 :: 57 :: r); match p.2 with
    | c :: _ => if isIdPart c then Except.error "number followed by an identifier character"
                else Except.ok (p.1, p.2)
    | [] => Except.ok (p.1, p.2)) = _
  rw [hs]
  simp only [hc, ↓reduceIte]

theorem split_glued_dot (b c : UInt8) (r digits suffix : Bytes)
    (hd : isDigit b = true)
    (hs : numberSpan false (46 :: b :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    split .sol (46 :: b :: r) = .error "number followed by an identifier character" := by
  have hn := hd
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hn
  have hb : b.toNat = 48 ∨ b.toNat = 49 ∨ b.toNat = 50 ∨ b.toNat = 51 ∨ b.toNat = 52 ∨ b.toNat = 53 ∨ b.toNat = 54 ∨ b.toNat = 55 ∨ b.toNat = 56 ∨ b.toNat = 57 := by omega
  rcases hb with h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57
  · have he : b = 48 := UInt8.toNat_inj.mp h48
    subst b
    exact split_glued_dot_48 r digits suffix c hs hc
  · have he : b = 49 := UInt8.toNat_inj.mp h49
    subst b
    exact split_glued_dot_49 r digits suffix c hs hc
  · have he : b = 50 := UInt8.toNat_inj.mp h50
    subst b
    exact split_glued_dot_50 r digits suffix c hs hc
  · have he : b = 51 := UInt8.toNat_inj.mp h51
    subst b
    exact split_glued_dot_51 r digits suffix c hs hc
  · have he : b = 52 := UInt8.toNat_inj.mp h52
    subst b
    exact split_glued_dot_52 r digits suffix c hs hc
  · have he : b = 53 := UInt8.toNat_inj.mp h53
    subst b
    exact split_glued_dot_53 r digits suffix c hs hc
  · have he : b = 54 := UInt8.toNat_inj.mp h54
    subst b
    exact split_glued_dot_54 r digits suffix c hs hc
  · have he : b = 55 := UInt8.toNat_inj.mp h55
    subst b
    exact split_glued_dot_55 r digits suffix c hs hc
  · have he : b = 56 := UInt8.toNat_inj.mp h56
    subst b
    exact split_glued_dot_56 r digits suffix c hs hc
  · have he : b = 57 := UInt8.toNat_inj.mp h57
    subst b
    exact split_glued_dot_57 r digits suffix c hs hc

theorem lex_glued_dot (b c : UInt8) (r digits suffix : Bytes)
    (hd : isDigit b = true)
    (hs : numberSpan false (46 :: b :: r) = (digits, c :: suffix)) (hc : isIdPart c = true) :
    lex (46 :: b :: r) = .error ⟨0, "number followed by an identifier character"⟩ := by
  have hg := split_glued_dot b c r digits suffix hd hs hc
  unfold lex
  rw [scan, hg]
  simp only [Nat.sub_self]
  all_goals exact List.cons_ne_nil _ _

end Solidity.Frontend.NumericLiteralProofs
