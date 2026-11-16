import Solidity.Goals.ProseCalibrated

/-! Classification and lexical padding laws for the frozen calibrated model.
These proofs do not establish checker correspondence or generator reproduction. -/
namespace Solidity.Goals.ProseCalibrated
namespace Classification

open ProseRatio (Category Segment Line)

theorem symmetricExclusion : ∀ (s : Scope) (f : File), verified s f = true →
    codeFile s f = 0 ∧ ∀ k, proseFile s f k = 0 := by
  intro s f h
  simp [codeFile, proseFile, eligible, h]

theorem headerInert : ∀ (s : Scope) (f : File) (b : Bool),
    eligible s { f with generationHeader := b } = eligible s f := by
  intros
  rfl

theorem unverifiedCounted : ∀ (s : Scope) (f : File), verified s f = false →
    s.kind f.path ≠ .outside → eligible s f = true := by
  intro s f hv hk
  simp [eligible, hv, hk]

theorem identityMismatch : ∀ (e : GeneratedEntry) (f : File),
    (e.path ≠ f.path ∨ e.outputBlob ≠ f.outputBlob ∨
    e.generatorPath ≠ f.generatorPath ∨ e.generatorBlob ≠ f.generatorBlob) →
    entryMatches e f = false := by
  intro e f h
  rcases h with h | h | h | h <;> simp [entryMatches, h]

private theorem line_subset (l : Line) : l.prose .docstring ≤ l.prose .comment := by
  have h : l.any Segment.isDocstring = true →
      l.any (fun s => s.isComment || s.isDocstring) = true := by
    simp only [List.any_eq_true]
    rintro ⟨s, hs, hd⟩
    exact ⟨s, hs, by simp [hd]⟩
  simp only [ProseRatio.Line.prose]
  split <;> split <;> simp_all

private theorem sum_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem docstringSubset : ∀ (s : Scope) (f : File),
    proseFile s f .docstring ≤ proseFile s f .comment := by
  intro s f
  simp only [proseFile]
  split
  · exact Nat.le_refl 0
  · cases s.kind f.path <;> simp only [Category.noConfusion, reduceCtorEq, ↓reduceIte]
    · exact sum_mono _ _ _ (fun x _ => line_subset x.1)
    · exact Nat.le_refl 0
    · exact Nat.le_refl 0

theorem sourceLocal : ∀ (s : Scope) (t : Tree) (a : RepoPath) (f : File),
    s.denominator a = .self → s.area f.path ≠ a →
    denominator s (t ++ [f]) a = denominator s t a := by
  intro s t a f hd ha
  simp [denominator, hd, ha, List.filter_append, List.map_append, List.sum_append_nat]

theorem docsRepository : ∀ (s : Scope) (t : Tree) (a : RepoPath),
    s.denominator a = .repositorySolidity →
    denominator s t a =
      (t.filter (fun f => f.path.head? == some "Solidity") |>.map (codeFile s)).sum := by
  intro s t a h
  simp only [denominator, h]

private theorem numerator_append (s : Scope) (t : Tree) (f : File) (a : RepoPath)
    (k : Category) : numerator s (t ++ [f]) a k = numerator s t a k +
      (if s.area f.path == a then proseFile s f k else 0) := by
  simp only [numerator, List.filter_append, List.map_append, List.sum_append_nat]
  by_cases h : s.area f.path == a <;> simp [List.filter_cons, h]

private theorem denominator_append (s : Scope) (t : Tree) (f : File) (a : RepoPath) :
    denominator s (t ++ [f]) a = denominator s t a +
      (if (match s.denominator a with
        | .self => s.area f.path == a
        | .repositorySolidity => f.path.head? == some "Solidity") then codeFile s f else 0) := by
  simp only [denominator, List.filter_append, List.map_append, List.sum_append_nat]
  cases s.denominator a <;> simp only [List.filter_cons] <;> split <;> simp_all

private theorem fits_zero (w : Allowance) (d : Nat) : w.fits 0 d = true := by
  simp [Allowance.fits]

private theorem fits_down (w : Allowance) (n m d : Nat) (h : n ≤ m)
    (hm : w.fits m d = true) : w.fits n d = true := by
  simp only [Allowance.fits, decide_eq_true_eq] at *
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)) hm

private theorem accepts_iff (p : Policy) (t : Tree) : accepts p t = true ↔
    ∀ a k, enforced a = true →
      (lookup p.entries (a,k)).fits (numerator p.scope t a k) (denominator p.scope t a) = true := by
  constructor
  · intro h a k he
    by_cases ha : a ∈ areas p t
    · have hk : k ∈ Category.all := by cases k <;> simp [Category.all]
      have hall := (List.all_eq_true.mp h) a ha
      simp only [he, Bool.not_true, Bool.false_or] at hall
      exact (List.all_eq_true.mp hall) k hk
    · have hz : numerator p.scope t a k = 0 := by
        have ht : ∀ f ∈ t, p.scope.area f.path ≠ a := by
          intro f hf heq
          apply ha
          simp only [areas, List.mem_append, List.mem_map]
          exact Or.inr ⟨f, hf, heq⟩
        unfold numerator
        have : t.filter (fun f => p.scope.area f.path == a) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro f hf
          simp [ht f hf]
        simp [this]
      rw [hz]
      exact fits_zero _ _
  · intro h
    apply List.all_eq_true.mpr
    intro a _
    by_cases he : enforced a = true
    · simp only [he, Bool.not_true, Bool.false_or]
      exact List.all_eq_true.mpr (fun k _ => h a k he)
    · simp [he]

theorem generatedPadding : ∀ (p : Policy) (t : Tree) (f : File),
    verified p.scope f = true → accepts p (t ++ [f]) = accepts p t := by
  intro p t f hv
  obtain ⟨hc, hp⟩ := symmetricExclusion p.scope f hv
  have hn : ∀ a k, numerator p.scope (t ++ [f]) a k = numerator p.scope t a k := by
    intro a k
    simp [numerator_append, hp]
  have hd : ∀ a, denominator p.scope (t ++ [f]) a = denominator p.scope t a := by
    intro a
    simp [denominator_append, hc]
  apply Bool.eq_iff_iff.mpr
  simp only [accepts_iff, hn, hd]

theorem codeFreePadding : ∀ (p : Policy) (t : Tree) (f : File),
    (∀ l ∈ f.lines, l.hasCode = false) →
    (∀ a, denominator p.scope (t ++ [f]) a = denominator p.scope t a) ∧
    (accepts p t = false → accepts p (t ++ [f]) = false) := by
  intro p t f h
  have hc : codeFile p.scope f = 0 := by
    have hz : (f.lines.map Line.code).sum = 0 := by
      have : f.lines.map Line.code = f.lines.map (fun _ => 0) := by
        apply List.map_congr_left
        intro l hl
        simp [ProseRatio.Line.code, h l hl]
      rw [this]
      induction f.lines with
      | nil => rfl
      | cons l ls ih => simpa using ih
    simp [codeFile, hz]
  have hd : ∀ a, denominator p.scope (t ++ [f]) a = denominator p.scope t a := by
    intro a
    simp [denominator_append, hc]
  refine ⟨hd, ?_⟩
  intro ht
  cases he : accepts p (t ++ [f]) with
  | false => rfl
  | true =>
    have old : accepts p t = true := by
      apply (accepts_iff _ _).mpr
      intro a k ha
      have hfit := (accepts_iff _ _).mp he a k ha
      rw [hd a] at hfit
      apply fits_down _ _ _ _ (by rw [numerator_append]; omega) hfit
    simp [ht] at old

end Classification
end Solidity.Goals.ProseCalibrated
