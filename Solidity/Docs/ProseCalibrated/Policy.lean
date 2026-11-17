import Solidity.Docs.ProseCalibrated.Allowance

/-! Acceptance, fail-closed and shrink laws for the frozen calibrated policy.
They concern the model's decision only, not checker correspondence. -/
namespace Solidity.Docs.ProseCalibrated

open Solidity.Goals.ProseCalibrated
open Solidity.Goals.ProseRatio (Category)

theorem allowance_value_le (w v : Allowance) (h : w.le v) (d : Nat) :
    (w.value d).le (v.value d) := by
  have hr := Nat.mul_le_mul_right d h.1
  have hm := h.2
  change (w.ratio.num * d * w.margin.den + w.margin.num * w.ratio.den) *
      (v.ratio.den * v.margin.den) ≤
    (v.ratio.num * d * v.margin.den + v.margin.num * v.ratio.den) *
      (w.ratio.den * w.margin.den)
  have hr' := Nat.mul_le_mul_right (w.margin.den * v.margin.den) hr
  have hm' := Nat.mul_le_mul_right (w.ratio.den * v.ratio.den) hm
  calc
    _ = (w.ratio.num * v.ratio.den * d) * (w.margin.den * v.margin.den) +
        (w.margin.num * v.margin.den) * (w.ratio.den * v.ratio.den) := by
      simp only [Nat.add_mul]; congr 1 <;> ac_rfl
    _ ≤ (v.ratio.num * w.ratio.den * d) * (w.margin.den * v.margin.den) +
        (v.margin.num * w.margin.den) * (w.ratio.den * v.ratio.den) :=
      Nat.add_le_add hr' hm'
    _ = _ := by simp only [Nat.add_mul]; congr 1 <;> ac_rfl

theorem fits_mono (w v : Allowance) (h : w.le v) (n d : Nat)
    (hw : w.fits n d = true) : v.fits n d = true :=
  (exact v n d).mpr (rational_trans _ _ _ ((exact w n d).mp hw) (allowance_value_le w v h d))

theorem lookup_absent (es : Entries) (key : RepoPath × Category)
    (h : ∀ w, (key, w) ∉ es) : lookup es key = .zero := by
  unfold lookup
  rw [List.find?_eq_none.mpr]
  intro ⟨k, w⟩ he hk
  cases beq_iff_eq.mp hk
  exact h w he

theorem zero_le (x : Rational) : Rational.zero.le x := by
  simp only [Solidity.Goals.ProseRatio.Ratio.le, Rational.zero, Nat.zero_mul, Nat.zero_le]

/-- The acceptance loop is the universal per-area, per-category order. -/
theorem decides : ∀ (p : Policy) (t : Tree), accepts p t = true ↔ Within p t := by
  intro p t
  constructor
  · intro h a k he
    apply (exact _ _ _).mp
    by_cases ha : a ∈ areas p t
    · have hk : k ∈ Category.all := by cases k <;> simp [Category.all]
      have hall := (List.all_eq_true.mp h) a ha
      simp only [he, Bool.not_true, Bool.false_or] at hall
      exact (List.all_eq_true.mp hall) k hk
    · have hz : numerator p.scope t a k = 0 := by
        have hnil : t.filter (fun f => p.scope.area f.path == a) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro f hf heq
          exact ha (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨f, hf, beq_iff_eq.mp heq⟩)))
        simp only [numerator, hnil, List.map_nil, List.sum_nil]
      rw [hz]
      simp only [Allowance.fits, Nat.zero_mul, Nat.zero_le, decide_true]
  · intro h
    apply List.all_eq_true.mpr
    intro a _
    by_cases he : enforced a = true
    · simp only [he, Bool.not_true, Bool.false_or]
      exact List.all_eq_true.mpr (fun k _ => (exact _ _ _).mpr (h a k he))
    · simp only [he, Bool.not_false, Bool.true_or]

theorem rejects : ∀ (p : Policy) (t : Tree) (a : RepoPath) (k : Category), enforced a = true →
    ¬(lookup p.entries (a,k)).Within (numerator p.scope t a k) (denominator p.scope t a) →
    accepts p t = false := by
  intro p t a k he hn
  cases h : accepts p t
  · rfl
  · exact absurd ((decides p t).mp h a k he) hn

theorem unseen : ∀ (p : Policy) (t : Tree) (a : RepoPath) (k : Category),
    (∀ w, ((a,k),w) ∉ p.entries) → enforced a = true →
    accepts p t = true → numerator p.scope t a k = 0 := by
  intro p t a k hk he h
  have hf := (exact _ _ _).mpr ((decides p t).mp h a k he)
  rw [lookup_absent _ _ hk] at hf
  simp only [Allowance.fits, Allowance.zero, Rational.zero, Nat.mul_one, Nat.zero_mul,
    Nat.add_zero, decide_eq_true_eq] at hf
  omega

theorem unavailable : ∀ (p : Policy), decision p none = false := fun _ => rfl

theorem lookup_shrink (p : Policy) (q : Entries) (key : RepoPath × Category) :
    lookup (p.shrink q).entries key =
      match p.entries.find? (fun e => e.1 == key) with
      | some e => e.2.min (lookup q key)
      | none => .zero := by
  have hm : (p.shrink q).entries.find? (fun e => e.1 == key) =
      (p.entries.find? (fun e => e.1 == key)).map (fun e => (e.1, e.2.min (lookup q e.1))) := by
    simp only [Policy.shrink]
    rw [List.find?_map]
    rfl
  rw [lookup, hm]
  cases hf : p.entries.find? (fun e => e.1 == key) with
  | none => rfl
  | some e =>
    cases beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hf).1
    rfl

theorem shrinkValues : ∀ (p : Policy) (q : Entries) (key : RepoPath × Category),
    (lookup (p.shrink q).entries key).le (lookup p.entries key) ∧
    (lookup (p.shrink q).entries key).le (lookup q key) := by
  intro p q key
  rw [lookup_shrink]
  cases hf : p.entries.find? (fun e => e.1 == key) with
  | none =>
    have hp : lookup p.entries key = .zero := by simp only [lookup, hf]
    rw [hp]
    exact ⟨⟨rational_refl _, rational_refl _⟩, ⟨zero_le _, zero_le _⟩⟩
  | some e =>
    have hp : lookup p.entries key = e.2 := by simp only [lookup, hf]
    rw [hp]
    exact min_below _ _

theorem shrinkFrozen : ∀ (p : Policy) (q : Entries), (p.shrink q).scope = p.scope ∧
    (p.shrink q).entries.map (·.1) = p.entries.map (·.1) := by
  intro p q
  exact ⟨rfl, by simp only [Policy.shrink, List.map_map]; rfl⟩

theorem rational_min_of_le (x y : Rational) (h : y.le x) :
    (x.min y).le y ∧ y.le (x.min y) := by
  unfold Solidity.Goals.ProseRatio.Ratio.min
  split
  · rename_i hxy
    exact ⟨hxy, h⟩
  · exact ⟨rational_refl _, rational_refl _⟩

theorem shrinkExact : ∀ (p : Policy) (q : Entries),
    (∀ key, (lookup q key).le (lookup p.entries key)) →
    ∀ key, (lookup (p.shrink q).entries key).equiv (lookup q key) := by
  intro p q hq key
  have hk := hq key
  rw [lookup_shrink]
  cases hf : p.entries.find? (fun e => e.1 == key) with
  | none =>
    have hp : lookup p.entries key = .zero := by simp only [lookup, hf]
    rw [hp] at hk
    exact ⟨⟨zero_le _, zero_le _⟩, hk⟩
  | some e =>
    have hp : lookup p.entries key = e.2 := by simp only [lookup, hf]
    rw [hp] at hk
    have hr := rational_min_of_le _ _ hk.1
    have hm := rational_min_of_le _ _ hk.2
    exact ⟨⟨hr.1, hm.1⟩, ⟨hr.2, hm.2⟩⟩

theorem tighten : ∀ (p q : Policy) (t : Tree), q.scope = p.scope →
    (∀ key, (lookup q.entries key).le (lookup p.entries key)) →
    accepts q t = true → accepts p t = true := by
  intro p q t hs hle h
  apply (decides p t).mpr
  intro a k he
  have hq := (exact _ _ _).mpr ((decides q t).mp h a k he)
  rw [hs] at hq
  exact (exact _ _ _).mp (fits_mono _ _ (hle (a, k)) _ _ hq)

theorem noReplacement : ∀ (p : Policy) (q : Entries) (t : Tree),
    accepts (p.shrink q) t = true → accepts p t = true := fun p q t =>
  tighten p (p.shrink q) t (shrinkFrozen p q).1 (fun key => (shrinkValues p q key).1)

end Solidity.Docs.ProseCalibrated
