import Solidity.Frontend.NumericLiteralProofs.Classification

/-! # Exact consumed prefixes, source ranges and denomination separation -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem digits1_consumption_range {raw ds rest : Bytes}
    (h : digits1 raw = some (ds, rest)) :
    ∃ pre : Bytes, pre = raw.take (raw.length - rest.length) ∧
      raw.drop (raw.length - rest.length) = rest ∧ eraseUnderscores pre = ds ∧
      pre.length = raw.length - rest.length ∧ ds.length ≤ pre.length := by
  obtain ⟨pre, hr, he, _⟩ := (Digits.complete h).consumed
  have hl : raw.length = pre.length + rest.length := by rw [hr, List.length_append]
  have hd : raw.length - rest.length = pre.length := by omega
  refine ⟨pre, ?_, ?_, he, hd.symm, ?_⟩
  · rw [hd, hr, List.take_left]
  · rw [hd, hr, List.drop_left]
  · rw [← he]
    exact List.length_filter_le _ _

theorem locate_order (ps : List Piece) :
    ∀ (m : Mode) (o : Nat) (x : Located × Mode), x ∈ locate m o ps →
      o ≤ x.1.start ∧ x.1.start ≤ x.1.stop := by
  induction ps with
  | nil => intro m o x hx; simp only [locate, List.not_mem_nil] at hx
  | cons p ps ih =>
    intro m o x hx
    simp only [locate] at hx
    split at hx
    · rcases List.mem_cons.mp hx with hx | hx
      · subst hx
        exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
      · have hb := ih (m.next p.kind) (o + p.raw.length) x hx
        omega
    · have hb := ih (m.next p.kind) (o + p.raw.length) x hx
      omega

theorem Decimal.raw_nonempty {raw : Bytes} {n : NumLit} (h : Decimal raw n) : raw ≠ [] := by
  intro hr
  subst raw
  cases h with
  | mk hi hf hn ho he =>
    cases hi with
    | absent _ =>
      cases hf with
      | nil => rcases hn with hn | hn <;> exact hn rfl
    | present hd => cases hd

theorem Hexadecimal.raw_nonempty {raw : Bytes} {n : NumLit} (h : Hexadecimal raw n) :
    raw ≠ [] := by
  cases h
  exact List.cons_ne_nil _ _

/-- The exact numeric source slice has positive length, stays inside the
source, and carries the independent exact spelling derivation. -/
theorem lex_numeric_range {s : Bytes} {ps : List Piece} (h : lex s = .ok ps)
    {x : Located × Mode} (hx : x ∈ locate .sol 0 ps) {n : NumLit}
    (hm : x.2 = .sol) (ht : x.1.tok = .num n) :
    x.1.start < x.1.stop ∧ x.1.stop ≤ s.length ∧
      ((s.drop x.1.start).take (x.1.stop - x.1.start)).length = x.1.stop - x.1.start ∧
      (Hexadecimal ((s.drop x.1.start).take (x.1.stop - x.1.start)) n ∨
       Decimal ((s.drop x.1.start).take (x.1.stop - x.1.start)) n) := by
  have hs := lex_locate h x hx
  have hb := locate_order ps .sol 0 x hx
  have hc := hs.1
  rw [hm, ht] at hc
  have hg := classify_numeric hc
  have hn : (s.drop x.1.start).take (x.1.stop - x.1.start) ≠ [] := by
    rcases hg with hg | hg
    · exact hg.raw_nonempty
    · exact hg.raw_nonempty
  have hl : ((s.drop x.1.start).take (x.1.stop - x.1.start)).length =
      x.1.stop - x.1.start := by
    simp only [List.length_take, List.length_drop]
    omega
  have hp : 0 < ((s.drop x.1.start).take (x.1.stop - x.1.start)).length :=
    List.length_pos_iff.mpr hn
  exact ⟨by omega, hs.2, hl, hg⟩

theorem noGlue_tail (p : Piece) (ps : List Piece) (h : noGlue (p :: ps) = true) :
    noGlue ps = true := by
  cases ps with
  | nil => rfl
  | cons q ps => exact (Bool.and_eq_true_iff.mp h).2

theorem noGlue_suffix (pre ps : List Piece) (h : noGlue (pre ++ ps) = true) :
    noGlue ps = true := by
  induction pre with
  | nil => exact h
  | cons p pre ih => exact ih (noGlue_tail p (pre ++ ps) h)

theorem numeric_head_separation {p q : Piece} {ps : List Piece} {n : NumLit}
    (h : noGlue (p :: q :: ps) = true) (hk : p.kind = .tok (.num n)) :
    (q.raw.head?.map isIdPart |>.getD false) = false := by
  simp only [noGlue, hk] at h
  have hn := (Bool.and_eq_true_iff.mp h).1
  cases hh : (q.raw.head?.map isIdPart |>.getD false) with
  | false => rfl
  | true => rw [hh] at hn; cases hn

/-- Every glued identifier-character suffix is refused, at arbitrary position
in an otherwise arbitrary piece sequence. -/
theorem glued_numeric_refused (s : Bytes) (pre post : List Piece) (p q : Piece) (n : NumLit)
    (hk : p.kind = .tok (.num n))
    (hq : (q.raw.head?.map isIdPart |>.getD false) = true) :
    lex s ≠ .ok (pre ++ p :: q :: post) := by
  intro h
  have hs := lex_sound h
  have hg := noGlue_suffix pre (p :: q :: post) hs.2.2.2.1
  have hh := numeric_head_separation hg hk
  rw [hq] at hh
  cases hh

def denominationBytes : Denom → Bytes
  | .wei => ascii "wei"
  | .gwei => ascii "gwei"
  | .ether => ascii "ether"
  | .seconds => ascii "seconds"
  | .minutes => ascii "minutes"
  | .hours => ascii "hours"
  | .days => ascii "days"
  | .weeks => ascii "weeks"
  | .years => ascii "years"

theorem denomination_head (d : Denom) :
    ((denominationBytes d).head?.map isIdPart |>.getD false) = true := by
  cases d <;> decide +kernel

/-- All elementary denomination spellings require separation from a number.
This is lexical only: it does not admit a semantically excluded unit. -/
theorem denomination_separation (s : Bytes) (pre post : List Piece) (p q : Piece)
    (n : NumLit) (d : Denom) (hk : p.kind = .tok (.num n))
    (hq : q.raw = denominationBytes d) : lex s ≠ .ok (pre ++ p :: q :: post) := by
  apply glued_numeric_refused s pre post p q n hk
  rw [hq]
  exact denomination_head d

end Solidity.Frontend.NumericLiteralProofs
