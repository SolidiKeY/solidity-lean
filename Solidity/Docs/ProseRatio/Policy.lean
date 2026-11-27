import Solidity.Docs.ProseRatio.Classification

/-! Shrink-only updates and growth under a frozen policy. -/
namespace Solidity.Docs.ProseRatio
open Solidity.Goals.ProseRatio
variable {A : Type} [DecidableEq A]

theorem lookup_absent (es : Entries A) (key : A × Category)
    (h : ∀ w, (key, w) ∉ es) : es.allowance key = .zero := by
  unfold Entries.allowance
  rw [List.find?_eq_none.mpr]
  intro ⟨k, w⟩ he hk
  cases of_decide_eq_true hk
  exact h w he

theorem zeroCode (pol : Policy A) (t : Tree) (a : A) (k : Category)
    (h : code pol.scope t a = 0) :
    Within pol t a k ↔ prose pol.scope t a k ≤ (pol.allowance (a, k)).margin := by
  simp [Within, Allowance.lines, h]

theorem unlisted (pol : Policy A) (t : Tree) (a : A) (k : Category)
    (h : ∀ w, ((a, k), w) ∉ pol.entries) (ht : accepts pol t = true) :
    prose pol.scope t a k = 0 := by
  have hn := (decides pol t).mp ht a k
  unfold Within Policy.allowance at hn
  rw [lookup_absent _ _ h] at hn
  simpa [Allowance.lines, Allowance.zero] using hn

theorem lookup_shrink (pol : Policy A) (p : Entries A) (key : A × Category) :
    (pol.shrink p).allowance key =
      match pol.entries.find? (fun e => decide (e.1 = key)) with
      | some e => e.2.min (p.allowance key)
      | none => .zero := by
  have hm : (pol.shrink p).entries.find? (fun e => decide (e.1 = key)) =
      (pol.entries.find? (fun e => decide (e.1 = key))).map
        (fun e => (e.1, e.2.min (p.allowance e.1))) := by
    simp only [Policy.shrink]
    rw [List.find?_map]
    rfl
  rw [Policy.allowance, Entries.allowance, hm]
  cases hf : pol.entries.find? (fun e => decide (e.1 = key)) with
  | none => rfl
  | some e =>
    cases of_decide_eq_true (List.find?_eq_some_iff_append.mp hf).1
    rfl

theorem shrinkValues (pol : Policy A) (p : Entries A) (key : A × Category) :
    ((pol.shrink p).allowance key).le (pol.allowance key) ∧
    ((pol.shrink p).allowance key).le (p.allowance key) := by
  rw [lookup_shrink]
  cases hf : pol.entries.find? (fun e => decide (e.1 = key)) with
  | none =>
    have hp : pol.allowance key = .zero := by simp [Policy.allowance, Entries.allowance, hf]
    rw [hp]
    exact ⟨zero_le _, zero_le _⟩
  | some e =>
    have hp : pol.allowance key = e.2 := by simp [Policy.allowance, Entries.allowance, hf]
    rw [hp]
    exact min_below _ _

theorem shrinkExact (pol : Policy A) (p : Entries A)
    (h : ∀ key, (p.allowance key).le (pol.allowance key)) (key : A × Category) :
    ((pol.shrink p).allowance key).Equiv (p.allowance key) := by
  have hk := h key
  rw [lookup_shrink]
  cases hf : pol.entries.find? (fun e => decide (e.1 = key)) with
  | none =>
    have hp : pol.allowance key = .zero := by simp [Policy.allowance, Entries.allowance, hf]
    rw [hp] at hk
    exact ⟨zero_le _, hk⟩
  | some e =>
    have hp : pol.allowance key = e.2 := by simp [Policy.allowance, Entries.allowance, hf]
    rw [hp] at hk
    exact min_exact _ _ hk

theorem shrinkKeeps (pol : Policy A) (p : Entries A) :
    (pol.shrink p).scope = pol.scope ∧
    (pol.shrink p).entries.map (·.1) = pol.entries.map (·.1) := by
  exact ⟨rfl, by simp only [Policy.shrink, List.map_map]; rfl⟩

theorem tighten (pol q : Policy A) (t : Tree) (hs : q.scope = pol.scope)
    (h : ∀ key, (q.allowance key).le (pol.allowance key)) (ht : accepts q t = true) :
    accepts pol t = true := by
  apply (decides pol t).mpr
  intro a k
  have hn := (decides q t).mp ht a k
  unfold Within at *
  rw [hs] at hn
  exact Nat.le_trans hn (lines_mono _ _ (h (a, k)) _)

theorem noReplacement (pol : Policy A) (p : Entries A) (t : Tree) :
    accepts (pol.shrink p) t = true → accepts pol t = true :=
  tighten pol (pol.shrink p) t rfl (fun key => (shrinkValues pol p key).1)

theorem growth (pol : Policy A) (t : Tree) (f : File) (hf : pol.scope.treat f.path = .source)
    (h : ∀ k, let w := pol.allowance (pol.scope.area f.path, k)
      (f.lines.map (Line.prose · k)).sum * w.ratio.den ≤
        w.ratio.num * (f.lines.map Line.code).sum)
    (ht : accepts pol t = true) : accepts pol (t ++ [f]) = true := by
  apply (decides pol (t ++ [f])).mpr
  intro a k
  have hn := (rounding _ _ _).mp ((decides pol t).mp ht a k)
  apply (rounding _ _ _).mpr
  rw [prose_append, code_append]
  by_cases ha : pol.scope.area f.path = a
  · have hg := h k
    rw [ha] at hg
    simp only [if_pos ha, fileProse, fileCode, hf] at *
    simpa only [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Nat.add_le_add hn hg
  · simpa only [if_neg ha, Nat.add_zero] using hn

end Solidity.Docs.ProseRatio
