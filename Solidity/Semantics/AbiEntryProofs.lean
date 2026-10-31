import Solidity.Semantics.AbiEntry

/-!
# ABI entry decoding: eager and lazy agree

`mdec_cval`: whatever solc's eager (memory) decoder accepts, the lazy
calldata accesses of the same bytes accept, with the same typed value. The
calldata size is below `2^64`, so no address wraps. `verdict_run` reads it
at the entry: a body runs only on values that every lazy read of a calldata
parameter reproduces, and `verdict_revert` says a certified revert is exactly
an entry failure, before the body.
-/

namespace Solidity.AbiEntry
open Solidity.AbiEntry

/-- A reference's lazy value at the position its encoding starts. -/
def cvalAt (I : Input) (f : Nat) (s : Shape) (p : Nat) : Except Fail (Val s) :=
  if s.lengthPrefixed then cval I f s (p + 32) (load I.data p) else cval I f s p 0

theorem wrap_of_lt {a : Nat} (h : a < W) : wrap a = a := Nat.mod_eq_of_lt h

theorem lim_lt_W : lim < W := by decide

/-- `access_calldata_tail`'s offset check holds for every tail that fits. -/
theorem tailFits_of {size base rel tail : Nat} (hs : size ≤ lim) (hr : rel ≤ lim)
    (h : base + rel + tail ≤ size) : tailFits size base rel tail = true := by
  simp only [tailFits, slt, sub, toInt, decide_eq_true_eq]
  simp only [W, H, lim] at *
  by_cases ht : tail = 0
  · subst ht
    split <;> split <;> omega
  · split <;> split <;> omega

/-- `access_calldata_tail`'s region check holds for every region that fits. -/
theorem regionFits_of {size addr len stride : Nat} (hs : size ≤ lim)
    (h : addr + 32 + len * stride ≤ size) : regionFits size addr len stride = true := by
  simp only [regionFits, slt, sub, toInt, wrap, Bool.not_eq_true', decide_eq_false_iff_not]
  simp only [W, H, lim] at *
  split <;> split <;> omega

/-- What a successful eager decode of a dynamic value checked: room for its
tail, and for `bytes`/an array its length and element region. -/
theorem mdec_bounds {I : Input} {f : Nat} {e : Shape} {p a : Nat} {v : Val e} {a' : Nat}
    (h : mdec I f e p a = .ok (v, a')) (hd : e.dynamic = true) :
    p + e.tailSize ≤ I.size ∧
      (e.lengthPrefixed = true → load I.data p ≤ lim ∧
        p + 32 + load I.data p * e.stride ≤ I.size) := by
  cases f with
  | zero => simp [mdec] at h
  | succ f =>
    cases e with
    | word k => simp [Shape.dynamic] at hd
    | bytes =>
      simp only [mdec] at h
      all_goals repeat' (first | (simp at h; done) | split at h)
      simp only [Shape.tailSize, Shape.lengthPrefixed, Shape.stride, forall_const]
      omega
    | array e =>
      simp only [mdec] at h
      all_goals repeat' (first | (simp at h; done) | split at h)
      simp only [Shape.tailSize, Shape.lengthPrefixed, Shape.stride, forall_const]
      omega
    | fixed e n =>
      simp only [mdec] at h
      all_goals repeat' (first | (simp at h; done) | split at h)
      simp only [Shape.tailSize, Shape.lengthPrefixed, Bool.false_eq_true, false_implies, and_true]
      omega
    | tuple ms =>
      simp only [mdec] at h
      all_goals repeat' (first | (simp at h; done) | split at h)
      simp only [Shape.tailSize, Shape.lengthPrefixed, Bool.false_eq_true, false_implies, and_true]
      omega

/-- A dynamic element the eager decoder accepts at its unsigned offset passes
`access_calldata_tail` at the same place. -/
theorem tailRef_of_mdec {I : Input} {f : Nat} {e : Shape} {base ptr a : Nat} {v : Val e}
    {a' : Nat} (hs : I.size ≤ lim) (hr : load I.data ptr ≤ lim)
    (h : mdec I f e (base + load I.data ptr) a = .ok (v, a')) (hd : e.dynamic = true) :
    tailRef I e base ptr = .ok (if e.lengthPrefixed then
      (base + load I.data ptr + 32, load I.data (base + load I.data ptr))
      else (base + load I.data ptr, 0)) := by
  obtain ⟨ht, hl⟩ := mdec_bounds h hd
  have hw : wrap (base + load I.data ptr) = base + load I.data ptr :=
    wrap_of_lt (by simp only [lim, W] at *; omega)
  simp only [tailRef, tailFits_of hs hr (by omega), hw, if_true]
  cases hp : e.lengthPrefixed
  · simp
  · obtain ⟨hL, hreg⟩ := hl hp
    have hw2 : wrap (base + load I.data ptr + 32) = base + load I.data ptr + 32 :=
      wrap_of_lt (by simp only [lim, W] at *; omega)
    simp only [Nat.not_lt.mpr hL, if_false, regionFits_of hs hreg, hw2, if_true]

/-- The agreement, for the four mutually recursive readers at once. -/
theorem mdec_cval_all (I : Input) (hs : I.size ≤ lim) : ∀ f : Nat,
    (∀ (s : Shape) (p a : Nat) (v : Val s) (a' : Nat),
      mdec I f s p a = .ok (v, a') → cvalAt I f s p = .ok v) ∧
    (∀ (e : Shape) (base i n a : Nat) (vs : Seq e n) (a' : Nat),
      base + (i + n) * e.headSize ≤ I.size →
      mseq I f e base i n a = .ok (vs, a') → cseq I f e base i n = .ok vs) ∧
    (∀ (e : Shape) (base src a : Nat) (v : Val e) (a' : Nat),
      melem I f e base src a = .ok (v, a') → celem I f e base src = .ok v) ∧
    (∀ (ms : List Shape) (base pos a : Nat) (vs : Vals ms) (a' : Nat),
      base + pos + Shape.headsSize ms ≤ I.size →
      mmembers I f ms base pos a = .ok (vs, a') → cmembers I f ms base pos = .ok vs) := by
  intro f
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s p a v a' h; simp [mdec] at h
    · intro e base i n a vs a' _ h
      cases n with
      | zero => cases vs; simp [cseq]
      | succ n => simp [mseq] at h
    · intro e base src a v a' h; simp [melem] at h
    · intro ms base pos a vs a' _ h
      cases ms with
      | nil => cases vs; simp [cmembers]
      | cons m ms => simp [mmembers] at h
  | succ f ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s p a v a' h
      cases s with
      | word k =>
        simp only [mdec] at h
        split at h
        · rename_i hk
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [cvalAt, Shape.lengthPrefixed, Bool.false_eq_true, if_false, cval, hk,
            dif_pos]
        · simp at h
      | bytes =>
        simp only [mdec] at h
        all_goals repeat' (first | (simp at h; done) | split at h)
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [cvalAt, Shape.lengthPrefixed, if_true, cval]
      | array e =>
        simp only [mdec] at h
        split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i hb
                split at h
                · rename_i xs a2 hxs
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hb' : p + 32 + (0 + load I.data p) * e.headSize ≤ I.size := by
                    simp only [Nat.zero_add]; omega
                  simp only [cvalAt, Shape.lengthPrefixed, if_true, cval,
                    ih2 _ _ _ _ _ _ _ hb' hxs]
                · simp at h
        · simp at h
      | fixed e n =>
        simp only [mdec] at h
        split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i hb
                split at h
                · rename_i xs a2 hxs
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hb' : p + (0 + n) * e.headSize ≤ I.size := by
                    simp only [Nat.zero_add]; omega
                  simp only [cvalAt, Shape.lengthPrefixed, Bool.false_eq_true, if_false, cval,
                    ih2 _ _ _ _ _ _ _ hb' hxs]
                · simp at h
        · simp at h
      | tuple ms =>
        simp only [mdec] at h
        split at h
        · simp at h
        · rename_i hb
          split at h
          · simp at h
          · split at h
            · rename_i vs a2 hvs
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hb' : p + 0 + Shape.headsSize ms ≤ I.size := by omega
              simp only [cvalAt, Shape.lengthPrefixed, Bool.false_eq_true, if_false, cval,
                ih4 _ _ _ _ _ _ hb' hvs]
            · simp at h
    · intro e base i n a vs a' hb h
      cases n with
      | zero => cases vs; simp [cseq]
      | succ n =>
        simp only [mseq] at h
        split at h
        · simp at h
        · rename_i v a1 hv
          split at h
          · simp at h
          · rename_i vs' a2 hvs
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Nat.add_mul, Nat.one_mul] at hb
            have hw : wrap (base + i * e.headSize) = base + i * e.headSize :=
              wrap_of_lt (by simp only [lim, W] at *; omega)
            have hb' : base + (i + 1 + n) * e.headSize ≤ I.size := by
              simp only [Nat.add_mul, Nat.one_mul]; omega
            simp only [cseq, hw, ih3 _ _ _ _ _ _ hv, ih2 _ _ _ _ _ _ _ hb' hvs]
    · intro e base src a v a' h
      simp only [melem] at h
      simp only [celem]
      by_cases hd : e.dynamic = true
      · simp only [hd, if_true] at h ⊢
        split at h
        · simp at h
        · rename_i hr
          have hr' : load I.data src ≤ lim := Nat.not_lt.mp hr
          rw [tailRef_of_mdec hs hr' h hd]
          have hv := ih1 _ _ _ _ _ h
          simp only [cvalAt] at hv
          cases hp : e.lengthPrefixed <;> simp only [hp, Except.bind, if_false, if_true,
            Bool.false_eq_true] at hv ⊢ <;> exact hv
      · simp only [hd, if_false, Bool.false_eq_true] at h ⊢
        have hv := ih1 _ _ _ _ _ h
        have hp : e.lengthPrefixed = false := by
          cases e <;> simp_all [Shape.lengthPrefixed, Shape.dynamic]
        simpa only [cvalAt, hp] using hv
    · intro ms base pos a vs a' hb h
      cases ms with
      | nil => cases vs; simp [cmembers]
      | cons m ms =>
        simp only [mmembers] at h
        split at h
        · simp at h
        · rename_i v a1 hv
          split at h
          · simp at h
          · rename_i vs' a2 hvs
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Shape.headsSize] at hb
            have hw : wrap (base + pos) = base + pos :=
              wrap_of_lt (by simp only [lim, W] at *; omega)
            have hb' : base + (pos + m.headSize) + Shape.headsSize ms ≤ I.size := by omega
            simp only [cmembers, hw, ih3 _ _ _ _ _ _ hv, ih4 _ _ _ _ _ _ hb' hvs]

/-- **Agreement.** Whatever solc's eager memory decoder accepts, the lazy
calldata reads of the same bytes accept, with the same typed value. -/
theorem mdec_cval {I : Input} (hs : I.size ≤ lim) {f : Nat} {s : Shape} {p a : Nat}
    {v : Val s} {a' : Nat} (h : mdec I f s p a = .ok (v, a')) : cvalAt I f s p = .ok v :=
  (mdec_cval_all I hs f).1 s p a v a' h

/-- **Entry agreement for a calldata parameter.** If the parameter whose head
is at `4 + pos` decodes eagerly to `v` (as an eager copy would), then solc's
entry checks for it pass, and lazily reading the reference they produce
yields `v`: the lazy decoder never fails earlier and never sees another value. -/
theorem eager_cref {I : Input} (hs : I.size ≤ lim) {f : Nat} {s : Shape} {pos : Nat}
    {v : Val s} (h : eager I (f + 1) s pos = .ok v) :
    ∃ addr len, cref I s 4 pos = .ok (addr, len) ∧ cval I f s addr len = .ok v := by
  simp only [eager] at h
  split at h
  · rename_i v' a' hm
    simp only [Except.ok.injEq] at h
    subst h
    simp only [melem] at hm
    by_cases hd : s.dynamic = true
    · simp only [hd, if_true] at hm
      split at hm
      · simp at hm
      · rename_i hr
        have hv := mdec_cval hs hm
        obtain ⟨ht, hl⟩ := mdec_bounds hm hd
        simp only [cvalAt] at hv
        cases s with
        | word k => simp [Shape.dynamic] at hd
        | bytes =>
          obtain ⟨hL, hreg⟩ := hl rfl
          simp only [Shape.tailSize, Shape.stride] at ht hreg
          exact ⟨_, _, by simp only [cref, hd, if_true, hr, if_false, Shape.stride,
            show 4 + load I.data (4 + pos) + 31 < I.size by omega, Nat.not_lt.mpr hL,
            Nat.not_lt.mpr hreg], hv⟩
        | array e =>
          obtain ⟨hL, hreg⟩ := hl rfl
          simp only [Shape.tailSize, Shape.stride] at ht hreg
          exact ⟨_, _, by simp only [cref, hd, if_true, hr, if_false, Shape.stride,
            show 4 + load I.data (4 + pos) + 31 < I.size by omega, Nat.not_lt.mpr hL,
            Nat.not_lt.mpr hreg], hv⟩
        | fixed e n =>
          simp only [Shape.tailSize] at ht
          exact ⟨_, _, by simp only [cref, hd, if_true, hr, if_false, Nat.not_lt.mpr ht], hv⟩
        | tuple ms =>
          simp only [Shape.tailSize] at ht
          exact ⟨_, _, by simp only [cref, hd, if_true, hr, if_false, Nat.not_lt.mpr ht], hv⟩
    · simp only [hd, Bool.false_eq_true, if_false] at hm
      have hv := mdec_cval hs hm
      have hp : s.lengthPrefixed = false := by
        cases s <;> simp_all [Shape.lengthPrefixed, Shape.dynamic]
      simp only [cvalAt, hp, Bool.false_eq_true, if_false] at hv
      exact ⟨_, _, by simp only [cref, hd, Bool.false_eq_true, if_false], hv⟩
  · simp at h

/-- **Failure timing.** A certified revert is exactly a failure of the checks
solc runs before the body. -/
theorem verdict_revert_iff (I : Input) (f : Nat) (ps : List Param) :
    verdict I f ps = .revert ↔ entry I f ps = .error .revert := by
  constructor
  · intro h
    unfold verdict at h
    split at h
    · assumption
    all_goals (try split at h) <;> simp_all
  · intro h
    simp only [verdict, h]

/-- A body runs only after every entry check passed. -/
theorem verdict_run_entry {I : Input} {f : Nat} {ps : List Param}
    {vs : Vals (ps.map Param.shape)} (h : verdict I f ps = .run vs) :
    ∃ es, entry I f ps = .ok es ∧ bodyValues I f ps es 0 = .ok vs := by
  unfold verdict at h
  split at h <;> try simp at h
  rename_i es hes
  split at h
  · rename_i vs' hv
    simp only [Verdict.run.injEq] at h
    exact ⟨es, hes, h ▸ hv⟩
  · simp at h

end Solidity.AbiEntry

/-- info: 'Solidity.AbiEntry.mdec_cval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.AbiEntry.mdec_cval
/-- info: 'Solidity.AbiEntry.eager_cref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.AbiEntry.eager_cref
/-- info: 'Solidity.AbiEntry.verdict_revert_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.AbiEntry.verdict_revert_iff
/-- info: 'Solidity.AbiEntry.verdict_run_entry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.AbiEntry.verdict_run_entry
