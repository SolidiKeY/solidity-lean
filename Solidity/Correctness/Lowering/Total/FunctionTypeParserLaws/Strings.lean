import Lean.Elab.Tactic

/-!
# Function-signature parser laws: core `String` operations on character lists

Core has no lemmas for `String.startsWith`, `endsWith`, `drop`, `dropRight`,
`isEmpty` or `intercalate`, and they do not reduce in the kernel (UTF-8
positions, well-founded loops). Here each is proved, from its definition,
equal to a `List Char` operation on `String.mk l`:

* `drop_mk`, `dropRight_mk`, `isEmpty_mk`;
* `startsWith_mk`, `endsWith_mk` (each the `decide` of a list equation);
* `intercalate_mk` (`sepJoin`), `data_intercalate`.

Nothing here mentions the parser; the laws hold for every character list.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Str

open Lean Elab Tactic Meta in
/-- One unfolding of `String.substrEq`'s character loop. The loop is a private
`where` function of core, so no identifier names it; this only looks the
constant up (by its module, `Init.Data.String.Basic`: a toolchain change that
moves it fails here, loudly) and calls the ordinary `unfold`, whose proof the
kernel checks. -/
elab "unfold_substrEq_loop" : tactic => liftMetaTactic1 fun g => do
  return some (← Meta.unfoldTarget g
    (mkPrivateNameCore `Init.Data.String.Basic `String.substrEq.loop))

open Lean Elab Term in
/-- The same private loop, as a term (to state its law). -/
elab "substrEqLoop%" : term =>
  return mkConst (mkPrivateNameCore `Init.Data.String.Basic `String.substrEq.loop)

/-- The UTF-8 byte length of a character list. -/
def ulen : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + ulen cs

@[simp] theorem ulen_nil : ulen [] = 0 := rfl
@[simp] theorem ulen_cons (c : Char) (cs : List Char) :
    ulen (c :: cs) = c.utf8Size + ulen cs := rfl

theorem ulen_append (a b : List Char) : ulen (a ++ b) = ulen a + ulen b := by
  induction a with
  | nil => simp
  | cons c a ih => simp [ih, Nat.add_assoc]

theorem ulen_eq_zero {l : List Char} : ulen l = 0 ↔ l = [] := by
  cases l with
  | nil => simp
  | cons c cs => have := c.utf8Size_pos; simp; omega

theorem pos_zero_add (p : String.Pos) : 0 + p = p := by simp [String.Pos.ext_iff]

theorem utf8ByteSize_mk (l : List Char) : (String.mk l).utf8ByteSize = ulen l := by
  show String.utf8ByteSize.go l = ulen l
  induction l with
  | nil => rfl
  | cons c cs ih => simp [String.utf8ByteSize.go, ih, Nat.add_comm]

/-! ## Reading at, after and before a prefix boundary -/

theorem getAux_at (pre : List Char) (c : Char) (suf : List Char) (i : Nat) :
    String.utf8GetAux (pre ++ c :: suf) ⟨i⟩ ⟨i + ulen pre⟩ = c := by
  induction pre generalizing i with
  | nil => simp [String.utf8GetAux]
  | cons a pre ih =>
    have ha := a.utf8Size_pos
    have ne : (⟨i⟩ : String.Pos) ≠ ⟨i + (a.utf8Size + ulen pre)⟩ := by
      intro h; injection h; omega
    simp only [List.cons_append, String.utf8GetAux, ulen_cons, if_neg ne]
    have := ih (i + a.utf8Size)
    rwa [Nat.add_assoc] at this

theorem get_at (pre : List Char) (c : Char) (suf : List Char) :
    (String.mk (pre ++ c :: suf)).get ⟨ulen pre⟩ = c := by
  have := getAux_at pre c suf 0
  rwa [Nat.zero_add] at this

theorem prevAux_at (pre : List Char) (c : Char) (suf : List Char) (i : Nat) :
    String.utf8PrevAux (pre ++ c :: suf) ⟨i⟩ ⟨i + ulen pre + c.utf8Size⟩ = ⟨i + ulen pre⟩ := by
  induction pre generalizing i with
  | nil => simp [String.utf8PrevAux, String.Pos.le_iff]
  | cons a pre ih =>
    have ha := a.utf8Size_pos
    have hc := c.utf8Size_pos
    have nle : ¬ ((⟨i + (a.utf8Size + ulen pre) + c.utf8Size⟩ : String.Pos) ≤ (⟨i⟩ : String.Pos) + a) := by
      simp [String.Pos.le_iff]; omega
    simp only [List.cons_append, String.utf8PrevAux, ulen_cons, if_neg nle]
    have := ih (i + a.utf8Size)
    simpa [String.Pos.addChar_eq, Nat.add_assoc] using this

/-- The substring `String.toSubstring` builds of a character list. -/
def sub (l : List Char) : Substring := ⟨⟨l⟩, 0, ⟨ulen l⟩⟩

theorem toSubstring_mk (l : List Char) : (String.mk l).toSubstring = sub l := by
  simp [String.toSubstring, sub, String.endPos, utf8ByteSize_mk]

theorem next_sub (pre suf : List Char) :
    (sub (pre ++ suf)).next ⟨ulen pre⟩ = ⟨ulen pre + ulen (suf.take 1)⟩ := by
  cases suf with
  | nil => simp [sub, Substring.next, String.Pos.ext_iff]
  | cons c s =>
    have hc := c.utf8Size_pos
    have ne : ¬ ((0 : String.Pos) + ⟨ulen pre⟩ = ⟨ulen (pre ++ c :: s)⟩) := by
      simp [String.Pos.ext_iff, ulen_append]; omega
    simp only [sub, Substring.next, if_neg ne]
    have h0 : (0 : String.Pos) + ⟨ulen pre⟩ = ⟨ulen pre⟩ := by simp [String.Pos.ext_iff]
    simp [h0, String.next, get_at]

theorem nextn_sub (n : Nat) (pre suf : List Char) :
    (sub (pre ++ suf)).nextn n ⟨ulen pre⟩ = ⟨ulen pre + ulen (suf.take n)⟩ := by
  induction n generalizing pre suf with
  | zero => simp [Substring.nextn]
  | succ n ih =>
    rw [Substring.nextn, next_sub]
    cases suf with
    | nil => simpa using ih pre []
    | cons c s =>
      have := ih (pre ++ [c]) s
      simp only [List.append_assoc, List.singleton_append, ulen_append, ulen_cons, ulen_nil,
        Nat.add_zero] at this
      simpa [Nat.add_assoc] using this

theorem prev_sub (pre : List Char) (c : Char) (suf : List Char) :
    (sub (pre ++ c :: suf)).prev ⟨ulen pre + c.utf8Size⟩ = ⟨ulen pre⟩ := by
  have hc := c.utf8Size_pos
  have ne : ¬ ((0 : String.Pos) + ⟨ulen pre + c.utf8Size⟩ = 0) := by
    simp [String.Pos.ext_iff]; omega
  simp only [sub, Substring.prev, if_neg ne]
  have := prevAux_at pre c suf 0
  simp only [Nat.zero_add] at this
  simpa [pos_zero_add, String.prev] using this

theorem prevn_sub (n : Nat) (pre suf : List Char) :
    (sub (pre ++ suf)).prevn n ⟨ulen pre⟩ = ⟨ulen (pre.take (pre.length - n))⟩ := by
  induction n generalizing pre suf with
  | zero => simp [Substring.prevn]
  | succ n ih =>
    rw [Substring.prevn]
    rcases List.eq_nil_or_concat pre with rfl | ⟨q, c, rfl⟩
    · simp
    · have e : q.concat c ++ suf = q ++ c :: suf := by simp
      have u : ulen (q.concat c) = ulen q + c.utf8Size := by simp [ulen_append]
      rw [e, u, prev_sub, ih q (c :: suf)]
      have : (q.concat c).length - (n + 1) = q.length - n := by simp
      rw [this, List.concat_eq_append, List.take_append_of_le_length (Nat.sub_le _ _)]

/-! ## Extraction between prefix boundaries -/

theorem go₂_eq (mid suf : List Char) (j : Nat) :
    String.extract.go₂ (mid ++ suf) ⟨j⟩ ⟨j + ulen mid⟩ = mid := by
  induction mid generalizing j with
  | nil => cases suf <;> simp [String.extract.go₂]
  | cons c m ih =>
    have hc := c.utf8Size_pos
    have ne : (⟨j⟩ : String.Pos) ≠ ⟨j + (c.utf8Size + ulen m)⟩ := by
      intro h; injection h; omega
    simp only [List.cons_append, String.extract.go₂, ulen_cons, if_neg ne]
    have := ih (j + c.utf8Size)
    simpa [String.Pos.addChar_eq, Nat.add_assoc] using this

theorem go₁_eq (pre rest : List Char) (i : Nat) (e : String.Pos) :
    String.extract.go₁ (pre ++ rest) ⟨i⟩ ⟨i + ulen pre⟩ e
      = String.extract.go₂ rest ⟨i + ulen pre⟩ e := by
  induction pre generalizing i with
  | nil => cases rest <;> simp [String.extract.go₁, String.extract.go₂]
  | cons a pre ih =>
    have ha := a.utf8Size_pos
    have ne : (⟨i⟩ : String.Pos) ≠ ⟨i + (a.utf8Size + ulen pre)⟩ := by
      intro h; injection h; omega
    simp only [List.cons_append, String.extract.go₁, ulen_cons, if_neg ne]
    have := ih (i + a.utf8Size)
    simpa [String.Pos.addChar_eq, Nat.add_assoc] using this

theorem extract_mk (pre mid suf : List Char) :
    (String.mk (pre ++ mid ++ suf)).extract ⟨ulen pre⟩ ⟨ulen pre + ulen mid⟩ = ⟨mid⟩ := by
  by_cases h : ulen mid = 0
  · have := ulen_eq_zero.1 h
    subst this
    simp [String.extract]
  · have nge : ¬ (ulen pre ≥ ulen pre + ulen mid) := by omega
    have g := go₁_eq pre (mid ++ suf) 0 ⟨ulen pre + ulen mid⟩
    have g₂ := go₂_eq mid suf (ulen pre)
    simp only [Nat.zero_add] at g
    simp only [String.extract, if_neg nge, List.append_assoc]
    rw [show (0 : String.Pos) = ⟨0⟩ from rfl, g, g₂]

/-! ## `drop`, `dropRight`, `isEmpty` -/

theorem drop_mk (l : List Char) (n : Nat) : (String.mk l).drop n = ⟨l.drop n⟩ := by
  have nx := nextn_sub n [] l
  have ex := extract_mk (l.take n) (l.drop n) []
  simp only [List.append_nil, List.take_append_drop, List.nil_append, ulen_nil] at nx ex
  have tot : ulen (l.take n) + ulen (l.drop n) = ulen l := by
    rw [← ulen_append, List.take_append_drop]
  rw [tot] at ex
  simp only [String.drop, toSubstring_mk]
  simp only [sub, Substring.drop, Substring.toString] at nx ⊢
  rw [show (⟨0⟩ : String.Pos) = 0 from rfl] at nx
  rw [nx]
  simpa [pos_zero_add] using ex

theorem prevn_end (l : List Char) (n : Nat) :
    (sub l).prevn n ⟨(sub l).bsize⟩ = ⟨ulen (l.take (l.length - n))⟩ := by
  have := prevn_sub n l []
  simpa [sub, Substring.bsize] using this

theorem dropRight_mk (l : List Char) (n : Nat) :
    (String.mk l).dropRight n = ⟨l.take (l.length - n)⟩ := by
  have ex := extract_mk [] (l.take (l.length - n)) (l.drop (l.length - n))
  simp only [List.nil_append, List.take_append_drop, ulen_nil, Nat.zero_add] at ex
  simp only [String.dropRight, toSubstring_mk]
  have pv := prevn_end l n
  simp only [sub, Substring.dropRight, Substring.toString] at pv ⊢
  rw [pv]
  simpa [pos_zero_add] using ex

theorem isEmpty_mk (l : List Char) : (String.mk l).isEmpty = l.isEmpty := by
  cases l with
  | nil => rfl
  | cons c cs =>
    have hc := c.utf8Size_pos
    simp [String.isEmpty, String.endPos, utf8ByteSize_mk, String.Pos.ext_iff]
    omega

/-! ## Substring equality, `startsWith`, `endsWith` -/

theorem loop_eq (a b p₁ p₂ r₁ r₂ : List Char) (h : ulen a = ulen b) :
    substrEqLoop% ⟨p₁ ++ a ++ r₁⟩ ⟨p₂ ++ b ++ r₂⟩ ⟨ulen p₁⟩ ⟨ulen p₂⟩
      ⟨ulen p₁ + ulen a⟩ = decide (a = b) := by
  induction a generalizing b p₁ p₂ with
  | nil =>
    have : b = [] := ulen_eq_zero.1 h.symm
    subst this
    unfold_substrEq_loop
    simp
  | cons c a ih =>
    have hc := c.utf8Size_pos
    cases b with
    | nil => simp at h; omega
    | cons d b =>
      unfold_substrEq_loop
      have lt : ulen p₁ < ulen p₁ + ulen (c :: a) := by simp; omega
      simp only [dif_pos lt, List.append_assoc, List.cons_append, get_at]
      by_cases cd : c = d
      · subst cd
        have h' : ulen a = ulen b := by simpa using h
        have := ih b (p₁ ++ [c]) (p₂ ++ [c]) h'
        simp only [List.append_assoc, List.singleton_append, ulen_append, ulen_cons, ulen_nil,
          Nat.add_zero] at this
        simpa [String.Pos.addChar_eq, Nat.add_assoc] using this
      · simp [cd]

/-- Equality of the substrings cut at prefix boundaries is equality of the
character lists between them. -/
theorem beq_cut (p₁ a r₁ b : List Char) :
    ((⟨⟨p₁ ++ a ++ r₁⟩, ⟨ulen p₁⟩, ⟨ulen p₁ + ulen a⟩⟩ : Substring) == sub b) = decide (a = b) := by
  show Substring.beq _ _ = _
  simp only [Substring.beq, Substring.bsize, sub]
  by_cases h : ulen a = ulen b
  · have l := loop_eq a b p₁ [] r₁ [] h
    simp only [List.nil_append, List.append_nil, ulen_nil] at l
    simp [h, String.substrEq, String.endPos, utf8ByteSize_mk, ulen_append]
    rw [← h]
    simpa using l
  · have : a ≠ b := fun e => h (e ▸ rfl)
    simp [h, this]

theorem startsWith_mk (l p : List Char) :
    (String.mk l).startsWith ⟨p⟩ = decide (l.take p.length = p) := by
  have nx := nextn_sub p.length [] l
  have bq := beq_cut [] (l.take p.length) (l.drop p.length) p
  simp only [List.nil_append, List.take_append_drop, ulen_nil, Nat.zero_add] at nx bq
  simp only [String.startsWith, toSubstring_mk, String.length_mk]
  simp only [sub, Substring.take] at nx ⊢
  rw [show (⟨0⟩ : String.Pos) = 0 from rfl] at nx
  rw [nx]
  simpa [sub, pos_zero_add] using bq

theorem endsWith_mk (l p : List Char) :
    (String.mk l).endsWith ⟨p⟩ = decide (l.drop (l.length - p.length) = p) := by
  have bq := beq_cut (l.take (l.length - p.length)) (l.drop (l.length - p.length)) [] p
  have tot : ulen (l.take (l.length - p.length)) + ulen (l.drop (l.length - p.length)) = ulen l := by
    rw [← ulen_append, List.take_append_drop]
  simp only [List.append_nil, List.take_append_drop, tot] at bq
  simp only [String.endsWith, toSubstring_mk, String.length_mk]
  have pv := prevn_end l p.length
  simp only [sub, Substring.takeRight] at pv ⊢
  rw [pv]
  simpa [sub, pos_zero_add] using bq

/-! ## `intercalate` -/

/-- `String.intercalate` on character lists. -/
def sepJoin (sep : List Char) : List (List Char) → List Char
  | [] => []
  | [a] => a
  | a :: b :: r => a ++ sep ++ sepJoin sep (b :: r)

theorem data_intercalate (s : String) (l : List String) :
    (s.intercalate l).data = sepJoin s.data (l.map String.data) := by
  cases l with
  | nil => rfl
  | cons a l =>
    induction l generalizing a with
    | nil => rfl
    | cons b l ih =>
      have e : s.intercalate (a :: b :: l) = s.intercalate ((a ++ s ++ b) :: l) := rfl
      have j : ∀ (x y : List Char) (r : List (List Char)),
          sepJoin s.data ((x ++ (s.data ++ y)) :: r) = x ++ (s.data ++ sepJoin s.data (y :: r)) := by
        intro x y r; cases r <;> simp [sepJoin]
      rw [e, ih (a ++ s ++ b)]
      simp [j, sepJoin]

theorem intercalate_mk (s : List Char) (l : List (List Char)) :
    (String.mk s).intercalate (l.map String.mk) = ⟨sepJoin s l⟩ := by
  apply String.ext
  simp [data_intercalate, Function.comp_def]

end Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Str
