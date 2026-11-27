import Solidity.Docs.ProseRatio.Allowance

/-! Classification and the universal interpretation of the acceptance loop. -/
namespace Solidity.Docs.ProseRatio
open Solidity.Goals.ProseRatio
variable {A : Type} [DecidableEq A]

private theorem sum_zero (l : List Nat) (h : ∀ n ∈ l, n = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.sum_cons, h n (by simp), Nat.zero_add]
    exact ih (fun n hn => h n (by simp [hn]))

omit [DecidableEq A] in
theorem uncounted_file (s : Scope A) (f : File) (h : (s.treat f.path).counted = false) :
    fileCode s f = 0 ∧ ∀ k, fileProse s f k = 0 := by
  cases ht : s.treat f.path <;> simp_all [Treatment.counted, fileCode, fileProse]

theorem absent_prose (s : Scope A) (t : Tree) (a : A) (ha : a ∉ checkedAreas s t) (k : Category) :
    prose s t a k = 0 := by
  unfold prose
  apply sum_zero
  intro n hn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
  obtain ⟨hft, heq⟩ := List.mem_filter.mp hf
  have he : s.area f.path = a := of_decide_eq_true heq
  have hc : (s.treat f.path).counted = false := by
    cases h : (s.treat f.path).counted
    · rfl
    · exact False.elim (ha (List.mem_map.mpr ⟨f, List.mem_filter.mpr ⟨hft, h⟩, he⟩))
  exact (uncounted_file s f hc).2 k

theorem decides (pol : Policy A) (t : Tree) : accepts pol t = true ↔ WithinAllowance pol t := by
  constructor
  · intro h a k
    by_cases ha : a ∈ checkedAreas pol.scope t
    · have hk : k ∈ Category.all := by cases k <;> simp [Category.all]
      have hf := List.all_eq_true.mp (List.all_eq_true.mp h a ha) k hk
      exact (rounding _ _ _).mpr (of_decide_eq_true hf)
    · unfold Within
      rw [absent_prose _ _ _ ha]
      exact Nat.zero_le _
  · intro h
    apply List.all_eq_true.mpr
    intro a _
    apply List.all_eq_true.mpr
    intro k _
    exact decide_eq_true ((rounding _ _ _).mp (h a k))

theorem rejects (pol : Policy A) (t : Tree) (a : A) (k : Category)
    (h : ¬ Within pol t a k) : accepts pol t = false := by
  cases he : accepts pol t
  · rfl
  · exact False.elim (h ((decides pol t).mp he a k))

theorem prose_append (s : Scope A) (t : Tree) (f : File) (a : A) (k : Category) :
    prose s (t ++ [f]) a k = prose s t a k +
      if s.area f.path = a then fileProse s f k else 0 := by
  simp [prose, List.filter_append, List.map_append, List.sum_append_nat]
  <;> split <;> simp_all

theorem code_append (s : Scope A) (t : Tree) (f : File) (a : A) :
    code s (t ++ [f]) a = code s t a +
      if s.area f.path = a then fileCode s f else 0 := by
  simp [code, List.filter_append, List.map_append, List.sum_append_nat]
  <;> split <;> simp_all

theorem uncounted (pol : Policy A) (t : Tree) (f : File)
    (h : (pol.scope.treat f.path).counted = false) : accepts pol (t ++ [f]) = accepts pol t := by
  have hz := uncounted_file pol.scope f h
  have hp : ∀ a k, prose pol.scope (t ++ [f]) a k = prose pol.scope t a k := by
    intro a k
    simp [prose_append, hz.2 k]
  have hc : ∀ a, code pol.scope (t ++ [f]) a = code pol.scope t a := by
    intro a
    simp [code_append, hz.1]
  have he : accepts pol (t ++ [f]) = true ↔ accepts pol t = true := by
    rw [decides, decides]
    simp only [WithinAllowance, Within, hp, hc]
  cases h₁ : accepts pol (t ++ [f]) <;> cases h₂ : accepts pol t <;> simp_all

theorem generatedPadding (pol : Policy A) (t : Tree) (f : File)
    (h : f.path ∈ pol.scope.generated) : accepts pol (t ++ [f]) = accepts pol t := by
  apply uncounted
  simp [Scope.treat, h, Treatment.counted]

theorem auditsPadding (pol : Policy A) (t : Tree) (f : File)
    (h : InAudits f.path = true) : accepts pol (t ++ [f]) = accepts pol t := by
  apply uncounted
  by_cases hg : f.path ∈ pol.scope.generated <;> simp [Scope.treat, h, hg, Treatment.counted]

theorem segmentInert (l : Line) (s : Segment) (h : s.isCode = false) :
    Line.hasCode (l ++ [s]) = l.hasCode ∧ Line.hasCode (s :: l) = l.hasCode := by
  simp [Line.hasCode, List.any_append, h]

theorem codeFreePadding (pol : Policy A) (t : Tree) (f : File)
    (h : ∀ l ∈ f.lines, l.hasCode = false) :
    (∀ a, code pol.scope (t ++ [f]) a = code pol.scope t a) ∧
    (accepts pol t = false → accepts pol (t ++ [f]) = false) := by
  have hz : fileCode pol.scope f = 0 := by
    unfold fileCode
    split
    · apply sum_zero
      intro n hn
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
      simp [Line.code, h l hl]
    · rfl
  have hc : ∀ a, code pol.scope (t ++ [f]) a = code pol.scope t a := by
    intro a
    simp [code_append, hz]
  refine ⟨hc, ?_⟩
  intro ht
  cases he : accepts pol (t ++ [f])
  · rfl
  · have hold : accepts pol t = true := (decides pol t).mpr (by
      intro a k
      have hn := (decides pol (t ++ [f])).mp he a k
      unfold Within at *
      rw [hc] at hn
      exact Nat.le_trans (by rw [prose_append]; omega) hn)
    simp_all

end Solidity.Docs.ProseRatio
