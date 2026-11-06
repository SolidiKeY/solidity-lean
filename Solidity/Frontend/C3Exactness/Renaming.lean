import Solidity.Frontend.C3Exactness.Trace

/-!
# Identity transport for exact C3

Injectivity is required only on a proved support predicate. This accommodates
existing declaration-position lookup without treating undeclared-name sentinels
as identities. Applications discharge support and injection from existing
admission and selection facts.
-/
namespace Solidity.Frontend.C3Exactness
variable {α β : Type}

/-- Injectivity on the actual identities represented by the input graph. -/
def InjectsOn (S : α → Prop) (f : α → β) : Prop :=
  ∀ a b, S a → S b → f a = f b → a = b

/-- Membership reflects through an identity map on its proved support. -/
theorem mem_map_reflect {S : α → Prop} {f : α → β} {l : List α} {x : α}
    (hf : InjectsOn S f) (hx : S x) (hl : ∀ a ∈ l, S a) :
    f x ∈ l.map f ↔ x ∈ l := by
  constructor
  · intro hm
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
    have he' : a = x := hf a x (hl a ha) hx he
    exact he' ▸ ha
  · intro hm
    exact List.mem_map.mpr ⟨x, hm, rfl⟩

variable [DecidableEq α] [DecidableEq β]

/-- Tail admissibility agrees under an injective identity representation. -/
theorem admissible_map {S : α → Prop} {f : α → β} {ls : List (List α)} {h : α}
    (hf : InjectsOn S f) (hs : ∀ x ∈ ls.flatten, S x) (hh : S h) :
    admissible (ls.map (List.map f)) (f h) = admissible ls h := by
  apply Bool.eq_iff_iff.mpr
  rw [admissible_iff, admissible_iff]
  constructor
  · intro hm l hl hin
    have hm' := hm (l.map f) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    apply hm'
    rw [← List.map_drop]
    exact List.mem_map.mpr ⟨h, hin, rfl⟩
  · intro hm l' hl' hin
    obtain ⟨l, hl, he⟩ := List.mem_map.mp hl'
    subst l'
    rw [← List.map_drop] at hin
    apply hm l hl
    exact (mem_map_reflect hf hh (fun x hx =>
      hs x (List.mem_flatten.mpr ⟨l, hl, List.mem_of_mem_drop hx⟩))).mp hin

/-- Empty-list normalization commutes with every identity map. -/
theorem active_map (f : α → β) (ls : List (List α)) :
    active (ls.map (List.map f)) = (active ls).map (List.map f) := by
  unfold active
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro l _
  simp only [Function.comp_apply, ne_eq, List.map_eq_nil_iff]

/-- Removing one identity commutes with its injective representation. -/
theorem filter_map_ne {S : α → Prop} {f : α → β} {l : List α} {h : α}
    (hf : InjectsOn S f) (hs : ∀ x ∈ l, S x) (hh : S h) :
    (l.map f).filter (· ≠ f h) = (l.filter (· ≠ h)).map f := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x hx
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  constructor
  · intro hn he
    exact hn (congrArg f he)
  · intro hn he
    exact hn (hf x h (hs x hx) hh he)

/-- Global C3 residual removal commutes with identity transport. -/
theorem residual_map {S : α → Prop} {f : α → β} {ls : List (List α)} {h : α}
    (hf : InjectsOn S f) (hs : ∀ x ∈ ls.flatten, S x) (hh : S h) :
    residual (ls.map (List.map f)) (f h) = (residual ls h).map (List.map f) := by
  simp only [residual, active_map, List.map_map]
  apply List.map_congr_left
  intro l hl
  exact filter_map_ne hf (fun x hx =>
    hs x (List.mem_flatten.mpr ⟨l, (List.mem_filter.mp hl).1, hx⟩)) hh

/-- A scanner respects pointwise candidate equality on its actual scan list. -/
theorem findSome_congr {γ δ : Type} (xs : List γ) (f g : γ → Option δ)
    (he : ∀ x ∈ xs, f x = g x) : xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?_cons]
    rw [he x List.mem_cons_self]
    cases hg : g x with
    | none => exact ih (fun y hy => he y (List.mem_cons_of_mem x hy))
    | some _ => rfl

/-- Mapping scanner results preserves its first-success convention. -/
theorem findSome_result_map {γ δ ε : Type} (f : δ → ε) (g : γ → Option δ) (xs : List γ) :
    xs.findSome? (fun x => (g x).map f) = (xs.findSome? g).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hg : g x <;>
      simp only [List.findSome?_cons, hg, Option.map_none, Option.map_some, ih]

/-- Exact first-head choice is preserved, including the rejected prefix. -/
theorem first_map {S : α → Prop} {f : α → β} {ls : List (List α)}
    (hf : InjectsOn S f) (hs : ∀ x ∈ ls.flatten, S x) :
    first (ls.map (List.map f)) = (first ls).map f := by
  unfold first
  rw [List.findSome?_map]
  change ls.findSome? (fun l => (l.map f).head?.filter
    (admissible (ls.map (List.map f)))) =
      (ls.findSome? (fun l => l.head?.filter (admissible ls))).map f
  apply Eq.trans (b := ls.findSome? (fun l => (l.head?.filter (admissible ls)).map f))
  · apply findSome_congr
    intro l hl
    cases hh : l.head? with
    | none => rw [List.head?_map, hh]; rfl
    | some h =>
      have hS : S h := hs h (List.mem_flatten.mpr ⟨l, hl, List.mem_of_mem_head? hh⟩)
      rw [List.head?_map, hh]
      simp only [Option.map_some]
      cases ha : admissible ls h <;>
        simp only [Option.filter_some, admissible_map hf hs hS, ha,
          Bool.false_eq_true, if_false, if_true, Option.map_none, Option.map_some]
  · exact findSome_result_map _ _ _

/-- Every successful trace transports to the existing injective identity representation. -/
theorem Trace.rename {S : α → Prop} {f : α → β} {ls : List (List α)} {out : List α}
    (ht : Trace ls out) (hf : InjectsOn S f) :
    (∀ x ∈ ls.flatten, S x) → Trace (ls.map (List.map f)) (out.map f) := by
  induction ht with
  | done he =>
    intro hs
    apply Trace.done
    rw [active_map, he]
    rfl
  | @step ls h out hc ht ih =>
    intro hs
    have hh : S h := hs h (first_mem hc)
    have hsa : ∀ x ∈ (active ls).flatten, S x := by rw [flatten_active]; exact hs
    have hc' : first (active (ls.map (List.map f))) = some (f h) := by
      rw [active_map, first_map hf hsa, hc, Option.map_some]
    have hsr : ∀ x ∈ (residual ls h).flatten, S x := by
      intro x hx
      rw [flatten_residual] at hx
      exact hs x (List.mem_filter.mp hx).1
    have hr := ih hsr
    rw [← residual_map hf hs hh] at hr
    exact Trace.step hc' hr

/-- Genuine ordering obstruction certificates transport to the same representation. -/
theorem Stuck.rename {S : α → Prop} {f : α → β} {ls : List (List α)}
    (ht : Stuck ls) (hf : InjectsOn S f) :
    (∀ x ∈ ls.flatten, S x) → Stuck (ls.map (List.map f)) := by
  induction ht with
  | @here ls ho =>
    intro hs
    have hsa : ∀ x ∈ (active ls).flatten, S x := by rw [flatten_active]; exact hs
    apply Stuck.here
    constructor
    · intro he
      rw [active_map] at he
      exact ho.1 (List.map_eq_nil_iff.mp he)
    · rw [active_map, first_map hf hsa, ho.2]
      rfl
  | @step ls h hc ht ih =>
    intro hs
    have hh : S h := hs h (first_mem hc)
    have hsa : ∀ x ∈ (active ls).flatten, S x := by rw [flatten_active]; exact hs
    have hc' : first (active (ls.map (List.map f))) = some (f h) := by
      rw [active_map, first_map hf hsa, hc, Option.map_some]
    have hsr : ∀ x ∈ (residual ls h).flatten, S x := by
      intro x hx
      rw [flatten_residual] at hx
      exact hs x (List.mem_filter.mp hx).1
    have hr := ih hsr
    rw [← residual_map hf hs hh] at hr
    exact Stuck.step hc' hr

/-- Identity representation preserves existence and failure of finite C3 traces. -/
theorem rename_exists_iff {S : α → Prop} {f : α → β} {ls : List (List α)}
    (hf : InjectsOn S f) (hs : ∀ x ∈ ls.flatten, S x) :
    (∃ out, Trace (ls.map (List.map f)) out) ↔ ∃ out, Trace ls out := by
  constructor
  · rintro ⟨out, ht⟩
    rcases trace_or_stuck ls with hsuccess | hstuck
    · exact hsuccess
    · exact False.elim ((hstuck.rename hf hs).not_trace ht)
  · rintro ⟨out, ht⟩
    exact ⟨out.map f, ht.rename hf hs⟩

end Solidity.Frontend.C3Exactness
