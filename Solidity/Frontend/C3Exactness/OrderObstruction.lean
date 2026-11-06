import Solidity.Frontend.C3Exactness.Trace

/-!
# Constructive ordering meaning of a C3 obstruction

A common order is duplicate-free and contains every input sequence as a
subsequence. Extra identities are allowed in this comparison order. A stuck
certificate excludes even such orders. Existence of a common order is weaker
than being the deterministic first-head C3 output.
-/
namespace Solidity.Frontend.C3Exactness
open Solidity.Source
variable {α : Type}

/-- A duplicate-free common supersequence; no producer call is used. -/
def CommonOrder (ls : List (List α)) (out : List α) : Prop :=
  out.Nodup ∧ ∀ l ∈ ls, l.Sublist out

variable [DecidableEq α]

/-- Every independent trace is a common order. -/
theorem Trace.common_order {ls : List (List α)} {out : List α}
    (ht : Trace ls out) : CommonOrder ls out :=
  ⟨ht.nodup, ht.local_order⟩

/-- A terminal obstruction excludes every duplicate-free common order. -/
theorem Obstruction.not_common_order {ls : List (List α)} (ho : Obstruction ls) :
    ∀ out, ¬ CommonOrder ls out := by
  intro out
  induction out with
  | nil =>
    intro hc
    cases ha : active ls with
    | nil => exact ho.1 ha
    | cons l rest =>
      have hl : l ∈ active ls := by
        rw [ha]
        exact List.mem_cons_self
      have hn : l ≠ [] := by
        simpa only [ne_eq, decide_eq_true_eq] using (List.mem_filter.mp hl).2
      exact hn (List.sublist_nil.mp (hc.2 l (List.mem_filter.mp hl).1))
  | cons h out ih =>
    intro hc
    have hn : h ∉ out := (List.nodup_cons.mp hc.1).1
    have htail : ∀ l ∈ ls, (l.drop 1).Sublist out := by
      intro l hl
      rcases List.sublist_cons_iff.mp (hc.2 l hl) with hs | ⟨tail, rfl, hs⟩
      · exact (List.drop_sublist 1 l).trans hs
      · exact hs
    by_cases hin : h ∈ ls.flatten
    · rcases List.mem_flatten.mp hin with ⟨l, hl, hm⟩
      have hnonempty : l ≠ [] := by
        intro he
        subst l
        cases hm
      have hactive : l ∈ active ls := List.mem_filter.mpr ⟨hl, by
        simpa only [ne_eq, decide_eq_true_eq] using hnonempty⟩
      have hhead : l.head? = some h := by
        rcases List.sublist_cons_iff.mp (hc.2 l hl) with hs | ⟨tail, rfl, hs⟩
        · exact False.elim (hn (hs.subset hm))
        · rfl
      rcases (first_none_iff (active ls)).mp ho.2 l hactive h hhead with
        ⟨blocking, hb, hblocked⟩
      exact hn ((htail blocking (List.mem_filter.mp hb).1).subset hblocked)
    · apply ih
      refine ⟨(List.nodup_cons.mp hc.1).2, ?_⟩
      intro l hl
      rcases List.sublist_cons_iff.mp (hc.2 l hl) with hs | ⟨tail, rfl, hs⟩
      · exact hs
      · exact False.elim (hin (List.mem_flatten.mpr
          ⟨h :: tail, hl, List.mem_cons_self⟩))

/-- Removing a chosen identity preserves any hypothetical common order. -/
theorem Stuck.not_common_order {ls : List (List α)} (ht : Stuck ls) :
    ∀ out, ¬ CommonOrder ls out := by
  induction ht with
  | here ho => exact ho.not_common_order
  | @step ls h _hf _ht ih =>
    intro out hc
    apply ih (out.filter (· ≠ h))
    refine ⟨List.Pairwise.filter _ hc.1, ?_⟩
    intro l hl
    rcases List.mem_map.mp hl with ⟨old, hold, rfl⟩
    exact List.Sublist.filter (· ≠ h) (hc.2 old (List.mem_filter.mp hold).1)

/-- Genuine obstruction is exactly incompatibility of the input order laws. -/
theorem stuck_iff_no_common_order (ls : List (List α)) :
    Stuck ls ↔ ¬ ∃ out, CommonOrder ls out := by
  constructor
  · rintro hs ⟨out, hc⟩
    exact hs.not_common_order out hc
  · intro hn
    rcases trace_or_stuck ls with ⟨out, ht⟩ | hs
    · exact False.elim (hn ⟨out, ht.common_order⟩)
    · exact hs

/-- Compatible order laws admit the deterministic trace, though not every
compatible order is that trace's output. -/
theorem trace_exists_iff_common_order (ls : List (List α)) :
    (∃ out, Trace ls out) ↔ ∃ out, CommonOrder ls out := by
  constructor
  · rintro ⟨out, ht⟩
    exact ⟨out, ht.common_order⟩
  · rintro ⟨out, hc⟩
    rcases trace_or_stuck ls with ht | hs
    · exact ht
    · exact False.elim (hs.not_common_order out hc)

/-- At finite sufficient fuel, failure is a genuine order-law inconsistency. -/
theorem merge_bound_none_iff_no_common_order (ls : List (List String)) :
    Env.merge (fuelBound ls) ls = none ↔ ¬ ∃ out, CommonOrder ls out := by
  rw [merge_bound_none_iff, stuck_iff_no_common_order]

/-- A common order exists exactly when the bounded producer succeeds. -/
theorem merge_bound_exists_iff_common_order (ls : List (List String)) :
    (∃ out, Env.merge (fuelBound ls) ls = some out) ↔
      ∃ out, CommonOrder ls out := by
  constructor
  · rintro ⟨out, hm⟩
    exact ⟨out, (merge_sound _ _ _ hm).common_order⟩
  · intro hc
    obtain ⟨out, ht⟩ := (trace_exists_iff_common_order ls).mpr hc
    exact ⟨out, (merge_bound_iff ls out).mpr ht⟩

/-- Every failed run is either an order-law obstruction or inadequate fuel for
the unique canonical trace. The existing producer and budget are unchanged. -/
theorem merge_none_iff_order_or_fuel (n : Nat) (ls : List (List String)) :
    Env.merge n ls = none ↔ (¬ ∃ out, CommonOrder ls out) ∨
      ∃ out, Trace ls out ∧ n ≤ out.length := by
  rw [merge_none_iff, stuck_iff_no_common_order]

end Solidity.Frontend.C3Exactness
