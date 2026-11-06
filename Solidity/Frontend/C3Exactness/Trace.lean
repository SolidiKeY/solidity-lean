import Solidity.Source.Resolve

/-!
# Exact, deterministic C3 merge traces

The relation never calls `Env.merge`. Residual empty lists are ignored; the
first admissible head is removed globally, and only an empty residual succeeds.
The relation is generic, including declaration-position identities (`Nat`).
The producer correspondence specializes it to contract-name strings; the
name-to-position graph lift remains a separate obligation.
-/
namespace Solidity.Frontend.C3Exactness
open Solidity.Source
variable {α : Type} [DecidableEq α]

/-- Nonempty residual lists, in their original order. -/
def active (ls : List (List α)) : List (List α) := ls.filter (· ≠ [])

/-- A candidate is admissible exactly when no residual tail contains it. -/
def admissible (ls : List (List α)) (h : α) : Bool :=
  ls.all fun l => !(l.drop 1).contains h

/-- Left-to-right selection; `findSome?` stops at the first admissible head. -/
def first (ls : List (List α)) : Option α :=
  ls.findSome? fun l => l.head?.filter (admissible ls)

/-- Remove every occurrence of the chosen identity in every active list. -/
def residual (ls : List (List α)) (h : α) : List (List α) :=
  (active ls).map fun l => l.filter (· ≠ h)

/-- Successful independent C3 trace, with no fuel parameter. -/
inductive Trace : List (List α) → List α → Prop where
  | done {ls} : active ls = [] → Trace ls []
  | step {ls h out} : first (active ls) = some h →
      Trace (residual ls h) out → Trace ls (h :: out)

/-- A genuine ordering obstruction: nonempty residuals with no legal head. -/
def Obstruction (ls : List (List α)) : Prop :=
  active ls ≠ [] ∧ first (active ls) = none

/-- A finite certificate ending at a genuine ordering obstruction. -/
inductive Stuck : List (List α) → Prop where
  | here {ls} : Obstruction ls → Stuck ls
  | step {ls h} : first (active ls) = some h → Stuck (residual ls h) → Stuck ls

/-- Empty residuals have no candidate. -/
theorem first_empty : first ([] : List (List α)) = none := rfl

/-- One positive unit of fuel unfolds exactly one independent trace step. -/
theorem merge_succ (n : Nat) (ls : List (List String)) :
    Env.merge (n + 1) ls =
      if (active ls).isEmpty then some [] else
        match first (active ls) with
        | none => none
        | some h => (Env.merge n (residual ls h)).map (h :: ·) := rfl

/-- Every successful implementation run produces an independent trace. -/
theorem merge_sound : ∀ (n : Nat) (ls : List (List String)) (out : List String),
    Env.merge n ls = some out → Trace ls out
  | 0, _, _, h => by cases h
  | n + 1, ls, out, h => by
    rw [merge_succ] at h
    split at h
    · rename_i he
      cases h
      exact .done (List.isEmpty_iff.mp he)
    · split at h
      · cases h
      · rename_i hd hf
        cases ho : Env.merge n (residual ls hd) with
        | none => rw [ho] at h; cases h
        | some rest =>
          rw [ho] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact .step hf (merge_sound n _ rest ho)

/-- A trace of length `k` succeeds with `k + 1` fuel, including termination. -/
theorem Trace.complete {ls : List (List String)} {out : List String}
    (t : Trace ls out) : ∀ n, out.length < n → Env.merge n ls = some out := by
  induction t with
  | done he =>
    intro n hn
    cases n with
    | zero => omega
    | succ n => rw [merge_succ, he]; rfl
  | @step ls hd out hf ht ih =>
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      have he : active ls ≠ [] := by
        intro he
        rw [he, first_empty] at hf
        cases hf
      rw [merge_succ, List.isEmpty_eq_false_iff.mpr he, hf]
      simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff]
      exact ⟨_, ih n (by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hn), rfl⟩

/-- Successful traces are unique directly from deterministic leftmost choice. -/
theorem Trace.unique {ls : List (List α)} {a b : List α}
    (ha : Trace ls a) (hb : Trace ls b) : a = b := by
  induction ha generalizing b with
  | done he =>
    cases hb with
    | done => rfl
    | step hf _ => rw [he, first_empty] at hf; cases hf
  | @step ls h out hf ht ih =>
    cases hb with
    | done he => rw [he, first_empty] at hf; cases hf
    | @step _ h' out' hf' ht' =>
      have eh : h = h' := Option.some.inj (hf.symm.trans hf')
      subst h'
      exact congrArg (h :: ·) (ih ht')

/-- Success requires a terminal observation after every emitted head. -/
theorem merge_fuel : ∀ (n : Nat) (ls : List (List String)) (out : List String),
    Env.merge n ls = some out → out.length < n
  | 0, _, _, h => by cases h
  | n + 1, ls, out, h => by
    rw [merge_succ] at h
    split at h
    · cases h; simp only [List.length_nil]; omega
    · split at h
      · cases h
      · rename_i hd hf
        cases ho : Env.merge n (residual ls hd) with
        | none => rw [ho] at h; cases h
        | some rest =>
          rw [ho] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have hr : rest.length < n := merge_fuel n _ rest ho
          simp only [List.length_cons]
          omega

/-- Exact correspondence at every fuel, including zero and the empty input. -/
theorem merge_iff {n : Nat} {ls : List (List String)} {out : List String} :
    Env.merge n ls = some out ↔ Trace ls out ∧ out.length < n :=
  ⟨fun h => ⟨merge_sound n ls out h, merge_fuel n ls out h⟩,
    fun h => h.1.complete n h.2⟩

/-- The admissibility test is precisely absence from every residual tail. -/
theorem admissible_iff (ls : List (List α)) (h : α) :
    admissible ls h = true ↔ ∀ l ∈ ls, h ∉ l.drop 1 := by
  simp only [admissible, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not]

/-- Selection explicitly records the rejected prefix before the chosen head. -/
theorem first_iff (ls : List (List α)) (h : α) :
    first ls = some h ↔ ∃ pre l post, ls = pre ++ l :: post ∧
      l.head?.filter (admissible ls) = some h ∧
      ∀ earlier ∈ pre, earlier.head?.filter (admissible ls) = none :=
  List.findSome?_eq_some_iff

/-- A selected head occurs in the original input, even with empty lists. -/
theorem first_mem {ls : List (List α)} {h : α}
    (hf : first (active ls) = some h) : h ∈ ls.flatten := by
  obtain ⟨l, hl, hs⟩ := List.exists_of_findSome?_eq_some hf
  have hh : l.head? = some h := (Option.filter_eq_some_iff.mp hs).1
  exact List.mem_flatten.mpr ⟨l, (List.mem_filter.mp hl).1, List.mem_of_mem_head? hh⟩

/-- Removing empty lists preserves the finite multiset of occurrences. -/
theorem flatten_active (ls : List (List α)) : (active ls).flatten = ls.flatten :=
  List.flatten_filter_ne_nil

/-- Global removal corresponds to filtering the concatenation. -/
theorem flatten_residual (ls : List (List α)) (h : α) :
    (residual ls h).flatten = ls.flatten.filter (· ≠ h) := by
  rw [residual, ← List.filter_flatten, flatten_active]

/-- Each selected head strictly decreases the total number of occurrences. -/
theorem residual_decreases {ls : List (List α)} {h : α}
    (hf : first (active ls) = some h) :
    (residual ls h).flatten.length < ls.flatten.length := by
  rw [flatten_residual]
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨h, first_mem hf, by simp only [ne_eq, not_true_eq_false, decide_false,
    Bool.false_eq_true, not_false_eq_true]⟩

/-- An arbitrary successful trace is bounded by the finite input occurrences. -/
theorem Trace.length_le {ls : List (List α)} {out : List α}
    (t : Trace ls out) : out.length ≤ ls.flatten.length := by
  induction t with
  | done => simp only [List.length_nil]; omega
  | step hf ht ih =>
    have hd := residual_decreases hf
    simp only [List.length_cons]
    omega

/-- Every finite input either has a successful trace or a finite obstruction certificate. -/
theorem trace_or_stuck (ls : List (List α)) : (∃ out, Trace ls out) ∨ Stuck ls := by
  suffices ∀ n (ls : List (List α)), ls.flatten.length = n →
      (∃ out, Trace ls out) ∨ Stuck ls from this _ ls rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ls hn
    by_cases he : active ls = []
    · exact .inl ⟨[], .done he⟩
    cases hf : first (active ls) with
    | none => exact .inr (.here ⟨he, hf⟩)
    | some hd =>
      have hlt : (residual ls hd).flatten.length < n := by
        rw [← hn]; exact residual_decreases hf
      rcases ih _ hlt (residual ls hd) rfl with ⟨out, ht⟩ | hs
      · exact .inl ⟨hd :: out, .step hf ht⟩
      · exact .inr (.step hf hs)

/-- Obstruction certificates exclude every successful deterministic trace. -/
theorem Stuck.not_trace {ls : List (List α)} (hs : Stuck ls) :
    ∀ {out}, ¬ Trace ls out := by
  induction hs with
  | here ho =>
    intro out ht
    cases ht with
    | done he => exact ho.1 he
    | step hf _ => rw [ho.2] at hf; cases hf
  | @step ls h hf hs ih =>
    intro out ht
    cases ht with
    | done he => rw [he, first_empty] at hf; cases hf
    | @step _ h' rest hf' ht' =>
      have eh : h = h' := Option.some.inj (hf.symm.trans hf')
      subst h'
      exact ih ht'

/-- A genuine ordering obstruction fails at every amount of implementation fuel. -/
theorem Stuck.merge_none {ls : List (List String)} (hs : Stuck ls) (n : Nat) :
    Env.merge n ls = none := by
  cases he : Env.merge n ls with
  | none => rfl
  | some out => exact False.elim (hs.not_trace (merge_sound n ls out he))

/-- At arbitrary fuel, failure is exactly obstruction or an insufficient trace budget. -/
theorem merge_none_iff {ls : List (List String)} {n : Nat} :
    Env.merge n ls = none ↔ Stuck ls ∨ ∃ out, Trace ls out ∧ n ≤ out.length := by
  constructor
  · intro hn
    rcases trace_or_stuck ls with ⟨out, ht⟩ | hs
    · right
      refine ⟨out, ht, ?_⟩
      by_cases hlt : n ≤ out.length
      · exact hlt
      · have he := ht.complete n (by omega)
        rw [hn] at he
        cases he
    · exact .inl hs
  · rintro (hs | ⟨out, ht, hlen⟩)
    · exact hs.merge_none n
    · cases he : Env.merge n ls with
      | none => rfl
      | some other =>
        have hu : out = other := ht.unique (merge_sound n ls other he)
        have hf : other.length < n := merge_fuel n ls other he
        subst other
        omega

/-- The finite input occurrence count plus one is a constructive sufficient fuel bound. -/
def fuelBound (ls : List (List α)) : Nat := ls.flatten.length + 1

/-- At the constructive input bound, failure means genuine C3 obstruction. -/
theorem merge_bound_none_iff (ls : List (List String)) :
    Env.merge (fuelBound ls) ls = none ↔ Stuck ls := by
  rw [merge_none_iff]
  constructor
  · rintro (hs | ⟨out, ht, hlen⟩)
    · exact hs
    · have hb : out.length ≤ ls.flatten.length := ht.length_le
      unfold fuelBound at hlen
      omega
  · exact Or.inl

/-- Exact merge/trace correspondence at the constructive finite-input bound. -/
theorem merge_bound_iff (ls : List (List String)) (out : List String) :
    Env.merge (fuelBound ls) ls = some out ↔ Trace ls out := by
  rw [merge_iff]
  exact ⟨And.left, fun ht => ⟨ht, by have hb := ht.length_le; unfold fuelBound; omega⟩⟩

/-- Exact membership is a property of the independent trace, at every identity type. -/
theorem Trace.mem_iff {ls : List (List α)} {out : List α}
    (t : Trace ls out) (x : α) : x ∈ out ↔ x ∈ ls.flatten := by
  induction t with
  | @done ls he =>
    have hm : ls.flatten = [] := by rw [← flatten_active, he]; rfl
    rw [hm]
  | @step ls h out hf ht ih =>
    rw [List.mem_cons, ih, flatten_residual, List.mem_filter]
    simp only [decide_eq_true_eq]
    constructor
    · rintro (he | hx)
      · subst x; exact first_mem hf
      · exact hx.1
    · intro hx
      by_cases he : x = h
      · exact .inl he
      · exact .inr ⟨hx, he⟩

/-- Global removal ensures that a successful trace never repeats an identity. -/
theorem Trace.nodup {ls : List (List α)} {out : List α}
    (t : Trace ls out) : out.Nodup := by
  induction t with
  | done => exact List.nodup_nil
  | @step ls h out hf ht ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro hm
    have hx := (ht.mem_iff h).mp hm
    rw [flatten_residual] at hx
    have hn := (List.mem_filter.mp hx).2
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true] at hn

/-- A chosen head is absent from every active tail. -/
theorem first_head {ls : List (List α)} {h : α} (hf : first ls = some h) :
    (∃ l ∈ ls, l.head? = some h) ∧ ∀ l ∈ ls, h ∉ l.drop 1 := by
  obtain ⟨l, hl, hs⟩ := List.exists_of_findSome?_eq_some hf
  obtain ⟨hh, ha⟩ := Option.filter_eq_some_iff.mp hs
  exact ⟨⟨l, hl, hh⟩, (admissible_iff ls h).mp ha⟩

/-- Removing an admissible head either peels that head or preserves the list. -/
theorem filter_head {l : List α} {h : α} (ht : h ∉ l.drop 1) :
    (l.head? = some h → l = h :: l.filter (· ≠ h)) ∧
      (h ∉ l → l.filter (· ≠ h) = l) := by
  constructor
  · intro hh
    cases l with
    | nil => cases hh
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [List.drop_one, List.tail_cons] at ht
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, if_false]
      rw [List.filter_eq_self.mpr (fun x hx => by
        simp only [decide_eq_true_eq]; intro he; subst he; exact ht hx)]
  · intro hn
    exact List.filter_eq_self.mpr (fun x hx => by
      simp only [ne_eq, decide_eq_true_eq]; intro he; subst he; exact hn hx)

/-- Every original list occurs in order in a successful independent trace. -/
theorem Trace.local_order {ls : List (List α)} {out : List α}
    (t : Trace ls out) : ∀ l ∈ ls, l.Sublist out := by
  induction t with
  | @done ls he =>
    intro l hl
    by_cases hn : l = []
    · subst l; exact List.Sublist.slnil
    · have hm : l ∈ active ls := List.mem_filter.mpr ⟨hl, by
        simpa only [ne_eq, decide_eq_true_eq] using hn⟩
      rw [he] at hm
      cases hm
  | @step ls h out hf ht ih =>
    intro l hl
    by_cases hn : l = []
    · subst l; exact List.nil_sublist _
    have hl' : l ∈ active ls := List.mem_filter.mpr ⟨hl, by
      simpa only [ne_eq, decide_eq_true_eq] using hn⟩
    have htail : h ∉ l.drop 1 := (first_head hf).2 l hl'
    have hsub : (l.filter (· ≠ h)).Sublist out :=
      ih _ (List.mem_map.mpr ⟨l, hl', rfl⟩)
    by_cases hin : h ∈ l
    · have hh : l.head? = some h := by
        cases l with
        | nil => cases hin
        | cons a tail =>
          rcases List.mem_cons.mp hin with he | hm
          · subst he; rfl
          · simp only [List.drop_one, List.tail_cons] at htail
            exact absurd hm htail
      rw [(filter_head htail).1 hh]
      exact hsub.cons₂ h
    · rw [← (filter_head htail).2 hin]
      exact hsub.cons h

/-- No selected head means every actual head has a concrete blocking tail. -/
theorem first_none_iff (ls : List (List α)) :
    first ls = none ↔ ∀ l ∈ ls, ∀ h, l.head? = some h →
      ∃ blocking ∈ ls, h ∈ blocking.drop 1 := by
  simp only [first, List.findSome?_eq_none_iff, Option.filter_eq_none_iff,
    admissible, Bool.not_eq_true, List.all_eq_false, Bool.not_eq_true,
    Bool.not_eq_false', List.contains_eq_mem, decide_eq_true_eq]

/-- A checked obstruction provides a nonempty residue and a blocker for every head. -/
theorem obstruction_iff (ls : List (List α)) :
    Obstruction ls ↔ active ls ≠ [] ∧ ∀ l ∈ active ls, ∀ h,
      l.head? = some h → ∃ blocking ∈ active ls, h ∈ blocking.drop 1 := by
  rw [Obstruction, first_none_iff]

end Solidity.Frontend.C3Exactness
