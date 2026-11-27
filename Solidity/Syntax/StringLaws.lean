import Init.Data.String.Lemmas
/-! Character-count bounds for the core UTF-8 string operations.
The extraction bounds also hold for arbitrary, possibly unaligned byte positions.
No parser or elaborator is imported here. -/
namespace Solidity.StringLaws
private theorem extract₂_le (cs : List Char) (i e : String.Pos) :
    (String.extract.go₂ cs i e).length ≤ cs.length := by
  induction cs generalizing i with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    simp only [String.extract.go₂]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (ih _)
private theorem extract₁_le (cs : List Char) (i b e : String.Pos) :
    (String.extract.go₁ cs i b e).length ≤ cs.length := by
  induction cs generalizing i with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    simp only [String.extract.go₁]
    split
    · exact extract₂_le _ _ _
    · exact Nat.le_trans (ih _) (Nat.le_succ _)
/-- Extraction cannot increase the number of Unicode code points. -/
theorem length_extract_le (s : String) (b e : String.Pos) :
    (s.extract b e).length ≤ s.length := by
  cases s with
  | mk cs =>
    simp only [String.extract]
    split
    · exact Nat.zero_le _
    · exact extract₁_le cs 0 b e
private theorem bytes_cons (c : Char) (cs : List Char) :
    (String.mk (c :: cs)).utf8ByteSize = c.utf8Size + (String.mk cs).utf8ByteSize := by
  simp only [String.utf8ByteSize, String.utf8ByteSize.go, Nat.add_comm]
private def Boundary (cs : List Char) (i p : String.Pos) : Prop :=
  match cs with
  | [] => i = p
  | c :: cs => i = p ∨ Boundary cs (i+c) p
private theorem valid_self (cs : List Char) (i : String.Pos) :
    Boundary cs i i := by
  cases cs <;> simp [Boundary]
private theorem valid_bounds (cs : List Char) (i p : String.Pos)
    (h : Boundary cs i p) :
    i.byteIdx ≤ p.byteIdx ∧ p.byteIdx ≤ i.byteIdx + (String.mk cs).utf8ByteSize := by
  induction cs generalizing i with
  | nil =>
    change i = p at h
    subst p
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons c cs ih =>
    rcases h with heq | h
    ·
      subst p
      exact ⟨Nat.le_refl _, Nat.le_add_right ..⟩
    · have hi := ih (i + c) h
      constructor
      · exact Nat.le_trans (Nat.le_add_right ..) hi.1
      · simpa only [String.Pos.addChar_eq, bytes_cons, Nat.add_assoc] using hi.2
private theorem valid_le (s : String) (p : String.Pos) (h : Boundary s.data 0 p) :
    p ≤ s.endPos := by
  cases s with
  | mk cs =>
    have hb := valid_bounds cs 0 p h
    change p.byteIdx ≤ (String.mk cs).utf8ByteSize
    simpa only [show (0 : String.Pos).byteIdx = 0 from rfl, Nat.zero_add] using hb.2
private theorem next_valid_go (cs : List Char) (i p : String.Pos)
    (h : Boundary cs i p)
    (hlt : p.byteIdx < i.byteIdx + (String.mk cs).utf8ByteSize) :
    Boundary cs i (p + String.utf8GetAux cs i p) := by
  induction cs generalizing i with
  | nil =>
    change i = p at h
    subst p
    exact False.elim ((Nat.lt_irrefl _) hlt)
  | cons c cs ih =>
    by_cases heq : i = p
    · subst p
      simp only [String.utf8GetAux]
      exact Or.inr (valid_self cs (i + c))
    · have h := h.resolve_left heq
      have ht : p.byteIdx < (i + c).byteIdx + (String.mk cs).utf8ByteSize := by
        simpa only [String.Pos.addChar_eq, bytes_cons, Nat.add_assoc] using hlt
      have hi := ih (i + c) h ht
      simp only [String.utf8GetAux, if_neg heq]
      exact Or.inr hi
private theorem next_valid (s : String) (p : String.Pos) (h : Boundary s.data 0 p)
    (hlt : p < s.endPos) : Boundary s.data 0 (s.next p) := by
  cases s with
  | mk cs =>
    change p.byteIdx < (String.mk cs).utf8ByteSize at hlt
    apply next_valid_go cs 0 p h
    simpa only [show (0 : String.Pos).byteIdx = 0 from rfl, Nat.zero_add] using hlt
private theorem extract₂_strict (cs : List Char) (i e : String.Pos)
    (h : Boundary cs i e)
    (hlt : e.byteIdx < i.byteIdx + (String.mk cs).utf8ByteSize) :
    (String.extract.go₂ cs i e).length < cs.length := by
  induction cs generalizing i with
  | nil =>
    change i = e at h
    subst e
    exact False.elim ((Nat.lt_irrefl _) hlt)
  | cons c cs ih =>
    by_cases heq : i = e
    · simp only [String.extract.go₂, if_pos heq, List.length_nil, List.length_cons]
      exact Nat.zero_lt_succ _
    · have h := h.resolve_left heq
      have ht : e.byteIdx < (i + c).byteIdx + (String.mk cs).utf8ByteSize := by
        simpa only [String.Pos.addChar_eq, bytes_cons, Nat.add_assoc] using hlt
      simp only [String.extract.go₂, if_neg heq, List.length_cons]
      exact Nat.succ_lt_succ (ih (i+c) h ht)
private theorem extract_strict_end (s : String) (e : String.Pos)
    (hv : Boundary s.data 0 e) (he : e < s.endPos) :
    (s.extract 0 e).length < s.length := by
  cases s with
  | mk cs =>
    cases cs with
    | nil => exact False.elim (Nat.not_lt_zero e.byteIdx he)
    | cons c cs =>
      simp only [String.extract]
      split
      · exact Nat.zero_lt_succ _
      · change (String.extract.go₁ (c :: cs) 0 0 e).length < (c :: cs).length
        simp only [String.extract.go₁]
        apply extract₂_strict (c :: cs) 0 e hv
        change e.byteIdx < (String.mk (c :: cs)).utf8ByteSize at he
        simpa only [show (0 : String.Pos).byteIdx = 0 from rfl, Nat.zero_add] using he
private theorem prev_valid_go (cs : List Char) (i p : String.Pos)
    (h : Boundary cs i p) (hp : i < p) :
    Boundary cs i (String.utf8PrevAux cs i p) ∧ String.utf8PrevAux cs i p < p := by
  induction cs generalizing i with
  | nil =>
    change i = p at h
    subst p
    exact False.elim ((Nat.lt_irrefl _) hp)
  | cons c cs ih =>
    simp only [String.utf8PrevAux]
    split
    · exact ⟨Or.inl rfl, hp⟩
    · rename_i hnot
      have hi : i ≠ p := by
        intro heq
        subst p
        exact (Nat.lt_irrefl _) hp
      have ht := h.resolve_left hi
      have hstep := ih (i+c) ht (Nat.lt_of_not_ge hnot)
      exact ⟨Or.inr hstep.1, hstep.2⟩
private theorem prev_valid (s : String) (p : String.Pos) (h : Boundary s.data 0 p)
    (hp : (0 : String.Pos) < p) :
    Boundary s.data 0 (s.prev p) ∧ s.prev p < p :=
  prev_valid_go s.data 0 p h hp
private theorem end_valid_go (cs : List Char) (i : String.Pos) :
    Boundary cs i ⟨i.byteIdx + (String.mk cs).utf8ByteSize⟩ := by
  induction cs generalizing i with
  | nil => exact String.Pos.ext (Nat.add_zero _).symm
  | cons c cs ih =>
    apply Or.inr
    simpa only [String.Pos.addChar_eq, bytes_cons, Nat.add_assoc] using ih (i+c)
private theorem end_valid (s : String) : Boundary s.data 0 s.endPos := by
  cases s with
  | mk cs =>
    simpa only [show (0 : String.Pos).byteIdx = 0 from rfl, Nat.zero_add] using end_valid_go cs 0
/-- A nonzero start discards at least one character of a nonempty string. -/
theorem length_extract_lt_of_start_ne_zero (s : String) (b e : String.Pos)
    (hb : b ≠ 0) (hs : 0 < s.length) :
    (s.extract b e).length < s.length := by
  cases s with
  | mk cs =>
    cases cs with
    | nil => exact False.elim (Nat.not_lt_zero _ hs)
    | cons c cs =>
      simp only [String.extract]
      split
      · exact hs
      · rw [String.extract.go₁, if_neg (Ne.symm hb)]
        exact Nat.lt_succ_of_le (extract₁_le cs _ b e)
private theorem nextn_ge (ss : Substring) (n : Nat) (p : String.Pos) :
    p.byteIdx ≤ (ss.nextn n p).byteIdx := by
  have step (q : String.Pos) : q.byteIdx ≤ (ss.next q).byteIdx := by
    cases ss with
    | mk s b e =>
      simp only [Substring.next]
      split
      · exact Nat.le_refl _
      · change q.byteIdx ≤ (b.byteIdx + q.byteIdx + (s.get (b + q)).utf8Size) - b.byteIdx
        rw [Nat.add_assoc, Nat.add_sub_cancel_left]
        exact Nat.le_add_right _ _
  induction n generalizing p with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.le_trans (step p) (ih _)
theorem length_drop_lt (s : String) (n : Nat) (hn : 0 < n)
    (hs : 0 < s.length) : (s.drop n).length < s.length := by
  have endNe : s.endPos ≠ 0 := by
    cases s with
    | mk cs =>
      cases cs with
      | nil => exact False.elim (Nat.not_lt_zero _ hs)
      | cons c cs =>
        intro h
        have hz := congrArg String.Pos.byteIdx h
        change String.utf8ByteSize.go cs + c.utf8Size = 0 at hz
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le c.utf8Size_pos (Nat.le_add_left _ _)) hz
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hn)
  | succ n =>
    have first : 0 < (s.toSubstring.next 0).byteIdx := by
      simp only [Substring.next, String.toSubstring]
      split
      · rename_i h
        exact False.elim (endNe (by simpa [String.Pos.ext_iff] using h.symm))
      · simpa [String.next] using (s.get 0).utf8Size_pos
    have positive := Nat.lt_of_lt_of_le first (nextn_ge s.toSubstring n _)
    apply length_extract_lt_of_start_ne_zero s _ _ _ hs
    intro h
    have hz := congrArg String.Pos.byteIdx h
    change 0 + (s.toSubstring.nextn n (s.toSubstring.next 0)).byteIdx = 0 at hz
    exact Nat.ne_of_gt positive (by simpa only [Nat.zero_add] using hz)
private theorem prev_toSubstring (s : String) (p : String.Pos) :
    s.toSubstring.prev p = s.prev p := by
  simp only [Substring.prev, String.toSubstring]
  split
  · rename_i h
    have hp : p = 0 := by simpa [String.Pos.ext_iff] using h
    subst p
    exact (String.prev_zero s).symm
  · have hz : (0 : String.Pos) + p = p := String.Pos.ext (Nat.zero_add _)
    change (⟨(s.prev ((0 : String.Pos) + p)).byteIdx - 0⟩ : String.Pos) = s.prev p
    rw [hz, Nat.sub_zero]
private theorem prevn_valid_le (s : String) (n : Nat) (p : String.Pos)
    (hv : Boundary s.data 0 p) :
    Boundary s.data 0 (s.toSubstring.prevn n p) ∧ s.toSubstring.prevn n p ≤ p := by
  induction n generalizing p with
  | zero => exact ⟨hv, Nat.le_refl _⟩
  | succ n ih =>
    rw [Substring.prevn, prev_toSubstring]
    by_cases hp : p = 0
    · subst p
      rw [String.prev_zero]
      exact ih 0 hv
    · have step := prev_valid s p hv (Nat.zero_lt_of_ne_zero (fun h => hp (String.Pos.ext h)))
      have rest := ih (s.prev p) step.1
      exact ⟨rest.1, Nat.le_trans rest.2 (Nat.le_of_lt step.2)⟩
/-- Removing a positive suffix strictly decreases a nonempty character measure. -/
theorem length_dropRight_lt (s : String) (n : Nat) (hn : 0 < n)
    (hs : 0 < s.length) : (s.dropRight n).length < s.length := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hn)
  | succ n =>
    have he : (0 : String.Pos) < s.endPos := by
      cases s with
      | mk cs =>
        cases cs with
        | nil => exact False.elim (Nat.not_lt_zero _ hs)
        | cons c cs =>
          exact Nat.lt_of_lt_of_le c.utf8Size_pos (Nat.le_add_left ..)
    have step := prev_valid s s.endPos (end_valid s) he
    have rest := prevn_valid_le s n (s.prev s.endPos) step.1
    have bound := Nat.lt_of_le_of_lt rest.2 step.2
    have h := extract_strict_end s (s.toSubstring.prevn n (s.prev s.endPos)) rest.1 bound
    have zero_add (q : String.Pos) : (0 : String.Pos) + q = q :=
      String.Pos.ext (Nat.zero_add _)
    change (s.extract 0 (0 + s.toSubstring.prevn (n+1) ⟨s.endPos.byteIdx - 0⟩)).length < s.length
    rw [Nat.sub_zero, zero_add, Substring.prevn, prev_toSubstring]
    exact h
/-- Even a substring with arbitrary byte bounds is bounded by its backing string. -/
theorem length_toString_le (ss : Substring) :
    ss.toString.length ≤ ss.str.length :=
  length_extract_le ss.str ss.startPos ss.stopPos
theorem length_drop_le (s : String) (n : Nat) :
    (s.drop n).length ≤ s.length :=
  length_toString_le (s.toSubstring.drop n)
theorem length_dropRight_le (s : String) (n : Nat) :
    (s.dropRight n).length ≤ s.length :=
  length_toString_le (s.toSubstring.dropRight n)
theorem length_take_le (s : String) (n : Nat) :
    (s.take n).length ≤ s.length :=
  length_toString_le (s.toSubstring.take n)
theorem length_takeRight_le (s : String) (n : Nat) :
    (s.takeRight n).length ≤ s.length :=
  length_toString_le (s.toSubstring.takeRight n)
theorem length_trim_le (s : String) : s.trim.length ≤ s.length :=
  length_toString_le s.toSubstring.trim
theorem length_trimLeft_le (s : String) : s.trimLeft.length ≤ s.length :=
  length_toString_le s.toSubstring.trimLeft
theorem length_trimRight_le (s : String) : s.trimRight.length ≤ s.length :=
  length_toString_le s.toSubstring.trimRight
private theorem splitOnAux_le (s sep : String) (b i j : String.Pos)
    (r : List String) (hr : ∀ x ∈ r, x.length ≤ s.length) :
    ∀ x ∈ s.splitOnAux sep b i j r, x.length ≤ s.length := by
  induction b, i, j, r using String.splitOnAux.induct s sep with
  | case1 b i j r h =>
    rw [String.splitOnAux, if_pos h]
    intro x hx
    simp only [List.mem_reverse, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact length_extract_le _ _ _
    · exact hr x hx
  | case2 b i j r h eq iNext jNext done ih =>
    dsimp only [iNext, jNext] at done ih
    rw [String.splitOnAux]
    simp only [h, eq, done, Bool.false_eq_true, ↓reduceIte]
    apply ih
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact length_extract_le _ _ _
    · exact hr x hx
  | case3 b i j r h eq iNext jNext more ih =>
    dsimp only [iNext, jNext] at more ih
    rw [String.splitOnAux]
    simpa only [h, eq, more, Bool.false_eq_true, ↓reduceIte] using ih hr
  | case4 b i j r h ne ih =>
    rw [String.splitOnAux]
    simpa only [h, ne, Bool.false_eq_true, ↓reduceIte] using ih hr
/-- Every piece of `splitOn`, including for an empty separator, is bounded. -/
theorem length_splitOn_le (s sep x : String) (hx : x ∈ s.splitOn sep) :
    x.length ≤ s.length := by
  unfold String.splitOn at hx
  split at hx
  · simp only [List.mem_singleton] at hx
    exact hx ▸ Nat.le_refl _
  · exact splitOnAux_le s sep 0 0 0 [] (by intro y hy; cases hy) x hx
private theorem next_sub_eq (s sep : String) (i j : String.Pos)
    (eq : (s.get i == sep.get j) = true) :
    s.next i - sep.next j = i - j := by
  apply String.Pos.ext
  change (i.byteIdx + (s.get i).utf8Size) - (j.byteIdx + (sep.get j).utf8Size) = _
  rw [(beq_iff_eq ..).1 eq, Nat.add_sub_add_right]
  rfl
private theorem splitOnAux_strict (s sep : String) (b i j : String.Pos) (r : List String)
    (hr : ∀ x ∈ r, x.length < s.length) (hb : r ≠ [] → b ≠ 0)
    (vi : Boundary s.data 0 i) (vm : Boundary s.data 0 (i-j))
    (vj : Boundary sep.data 0 j) (hj : j < sep.endPos) :
    1 < (s.splitOnAux sep b i j r).length →
    ∀ x ∈ s.splitOnAux sep b i j r, x.length < s.length := by
  induction b, i, j, r using String.splitOnAux.induct s sep with
  | case1 b i j r h =>
    rw [String.splitOnAux, if_pos h]
    intro hlen x hx
    simp only [List.mem_reverse, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have hrne : r ≠ [] := by
        intro he
        subst r
        exact (Nat.lt_irrefl 1) hlen
      have hs : 0 < s.length := by
        cases r with
        | nil => exact False.elim (hrne rfl)
        | cons a as => exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hr a (List.mem_cons_self))
      exact length_extract_lt_of_start_ne_zero s b i (hb hrne) hs
    · exact hr x hx
  | case2 b i j r h eq iNext jNext done ih =>
    dsimp only [iNext, jNext] at done ih
    have hiLt : i < s.endPos := Nat.gt_of_not_le (mt decide_eq_true h)
    have vn := next_valid s i vi hiLt
    have njpos : 0 < (sep.next j).byteIdx := Nat.lt_of_le_of_lt (Nat.zero_le _) (String.lt_next sep j)
    have nipos : 0 < (s.next i).byteIdx := Nat.lt_of_le_of_lt (Nat.zero_le _) (String.lt_next s i)
    have ve : Boundary s.data 0 (s.next i - sep.next j) := by
      rw [next_sub_eq s sep i j eq]
      exact vm
    have elt : s.next i - sep.next j < s.endPos :=
      Nat.lt_of_lt_of_le (Nat.sub_lt nipos njpos) (valid_le s (s.next i) vn)
    have hs : 0 < s.length := by
      cases s with
      | mk cs =>
        cases cs with
        | nil => exact False.elim (Nat.not_lt_zero i.byteIdx hiLt)
        | cons c cs => exact Nat.zero_lt_succ _
    have exlt : (s.extract b (s.next i - sep.next j)).length < s.length := by
      by_cases hb0 : b = 0
      · subst b
        exact extract_strict_end s _ ve elt
      · exact length_extract_lt_of_start_ne_zero s b _ hb0 hs
    rw [String.splitOnAux]
    simp only [h, eq, done, Bool.false_eq_true, ↓reduceIte]
    apply ih
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact exlt
      · exact hr x hx
    · intro _ heq
      exact Nat.ne_of_gt nipos (congrArg String.Pos.byteIdx heq)
    · exact vn
    · simpa only [show s.next i - (0 : String.Pos) = s.next i from String.Pos.ext (Nat.sub_zero _)] using vn
    · exact valid_self sep.data 0
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  | case3 b i j r h eq iNext jNext more ih =>
    dsimp only [iNext, jNext] at more ih
    have hiLt : i < s.endPos := Nat.gt_of_not_le (mt decide_eq_true h)
    have vn := next_valid s i vi hiLt
    have vjn := next_valid sep j vj hj
    have hn : sep.next j < sep.endPos := Nat.gt_of_not_le (mt decide_eq_true more)
    rw [String.splitOnAux]
    simp only [h, eq, more, Bool.false_eq_true, ↓reduceIte]
    apply ih hr hb vn
    · rw [next_sub_eq s sep i j eq]
      exact vm
    · exact vjn
    · exact hn
  | case4 b i j r h ne ih =>
    have hiLt : i < s.endPos := Nat.gt_of_not_le (mt decide_eq_true h)
    have hm : i-j < s.endPos := Nat.lt_of_le_of_lt (Nat.sub_le ..) hiLt
    have vn := next_valid s (i-j) vm hm
    rw [String.splitOnAux]
    simp only [h, ne, Bool.false_eq_true, ↓reduceIte]
    apply ih hr hb vn
    · simpa only [show (0 : String.Pos).byteIdx = 0 from rfl, String.Pos.ext_iff, Nat.sub_zero] using vn
    · exact valid_self sep.data 0
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hj
/-- When splitting finds a separator (there is more than one piece), every piece
is strictly shorter. The premise is exactly the non-singleton parser branch;
it also excludes the empty-separator case. -/
theorem length_splitOn_lt (s sep x : String) (hlen : 1 < (s.splitOn sep).length)
    (hx : x ∈ s.splitOn sep) : x.length < s.length := by
  unfold String.splitOn at hlen hx
  by_cases hn : (sep == "") = true
  · simp only [if_pos hn, List.length_singleton] at hlen
    exact False.elim ((Nat.lt_irrefl 1) hlen)
  · simp only [if_neg hn] at hlen hx
    have hp : (0 : String.Pos) < sep.endPos := by
      cases sep with
      | mk cs =>
        cases cs with
        | nil => exact False.elim (hn rfl)
        | cons c cs =>
          change 0 < (String.mk (c :: cs)).utf8ByteSize
          rw [bytes_cons]
          exact Nat.lt_of_lt_of_le c.utf8Size_pos (Nat.le_add_right ..)
    exact splitOnAux_strict s sep 0 0 0 [] (by intro y hy; cases hy)
      (by intro he; exact False.elim (he rfl)) (valid_self s.data 0)
      (valid_self s.data 0) (valid_self sep.data 0) hp hlen x hx
end Solidity.StringLaws
