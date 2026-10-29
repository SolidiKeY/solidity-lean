import Solidity.Source.Inheritance

/-!
# C3 linearization, specified and checked (G14)

S01 computes solc's C3 linearization (`Env.linearize`, `Env.merge`) but
states nothing about its result.  `C3Lin E c L` is the declarative
specification of a C3-consistent linearization of contract `c`
(`Solidity/Source/Inheritance.lean`):

- `L = c :: M` with `M` duplicate-free;
- every base's linearization (itself `C3Lin`) is an ordered sublist of `M`
  (monotonicity), and so is the list of direct bases, most derived first
  (local precedence: `is A, B` puts `B` before `A`);
- `M` holds nothing else.

`linearize_sound`: whatever S01's `Env.linearize` returns satisfies it.  The
merge laws behind it: an output contains every input element
(`merge_contains`), only input elements (`merge_sub`), keeps each input
list's order (`merge_sublist`) and has no duplicates (`merge_nodup`).
Completeness (C3 finds a linearization whenever one exists) is not claimed:
C3 is a particular choice, and solc refuses exactly when C3 fails.
-/

namespace Solidity.Frontend.Static

open Solidity.Source

/-- The head the merge picks satisfies C3's rule. -/
theorem merge_head {ls : List (List String)} {h : String}
    (hf : ls.findSome? (fun l => l.head?.filter fun h => ls.all fun l' => !(l'.drop 1).contains h) =
      Option.some h) :
    (∃ l, l ∈ ls ∧ l.head? = Option.some h) ∧ ∀ l', l' ∈ ls → h ∉ l'.drop 1 := by
  obtain ⟨l, hl, hs⟩ := List.exists_of_findSome?_eq_some hf
  cases hh : l.head? with
  | none => rw [hh] at hs; cases hs
  | some h' =>
    rw [hh] at hs
    simp only [Option.filter_some] at hs
    split at hs
    · rename_i hall
      cases hs
      refine ⟨⟨l, hl, hh⟩, fun l' hl' hm => ?_⟩
      have := (List.all_eq_true.mp hall) l' hl'
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
      exact this hm
    · cases hs

/-- Removing the chosen head `h` from a list where it is not in the tail:
the list's tail when `h` heads it, the list itself otherwise. -/
theorem filter_head {l : List String} {h : String} (ht : h ∉ l.drop 1) :
    (l.head? = Option.some h → l = h :: l.filter (· ≠ h)) ∧ (h ∉ l → l.filter (· ≠ h) = l) := by
  constructor
  · intro hh
    cases l with
    | nil => cases hh
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [List.drop_one, List.tail_cons] at ht
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      rw [List.filter_eq_self.mpr (fun x hx => by simp only [decide_eq_true_eq]; intro e; subst e; exact ht hx)]
  · intro hn
    exact List.filter_eq_self.mpr (fun x hx => by simp only [ne_eq, decide_eq_true_eq]; intro e; subst e; exact hn hx)

/-- The merge's output contains only input elements. -/
theorem merge_sub : ∀ (n : Nat) (ls : List (List String)) (out : List String), Env.merge n ls = Option.some out →
    ∀ x, x ∈ out → ∃ l, l ∈ ls ∧ x ∈ l
  | 0, _, _, h, _, _ => by cases h
  | n + 1, ls, out, h, x, hx => by
    unfold Env.merge at h
    simp only at h
    split at h
    · cases h; cases hx
    · split at h
      · cases h
      · rename_i hd hf
        cases ho : Env.merge n ((ls.filter (· ≠ [])).map fun l => l.filter (· ≠ hd)) with
        | none => rw [ho] at h; cases h
        | some out' =>
          rw [ho] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp hx with e | hx'
          · subst e
            obtain ⟨⟨l, hl, hh⟩, _⟩ := merge_head hf
            exact ⟨l, (List.mem_filter.mp hl).1, List.mem_of_mem_head? hh⟩
          · obtain ⟨l, hl, hxl⟩ := merge_sub n _ out' ho x hx'
            obtain ⟨l0, hl0, e⟩ := List.mem_map.mp hl
            subst e
            exact ⟨l0, (List.mem_filter.mp hl0).1, (List.mem_filter.mp hxl).1⟩

/-- The merge's output has no duplicates. -/
theorem merge_nodup : ∀ (n : Nat) (ls : List (List String)) (out : List String),
    Env.merge n ls = Option.some out → out.Nodup
  | 0, _, _, h => by cases h
  | n + 1, ls, out, h => by
    have h0 := h
    unfold Env.merge at h
    simp only at h
    split at h
    · cases h; exact List.nodup_nil
    · split at h
      · cases h
      · rename_i hd hf
        cases ho : Env.merge n ((ls.filter (· ≠ [])).map fun l => l.filter (· ≠ hd)) with
        | none => rw [ho] at h; cases h
        | some out' =>
          rw [ho] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          refine List.nodup_cons.mpr ⟨fun hm => ?_, merge_nodup n _ out' ho⟩
          obtain ⟨l, hl, hxl⟩ := merge_sub n _ out' ho hd hm
          obtain ⟨l0, _, e⟩ := List.mem_map.mp hl
          subst e
          simp only [List.mem_filter, ne_eq, decide_eq_true_eq, not_true_eq_false, and_false] at hxl

/-- The merge's output contains every input list as an ordered sublist. -/
theorem merge_sublist : ∀ (n : Nat) (ls : List (List String)) (out : List String),
    Env.merge n ls = Option.some out → ∀ l, l ∈ ls → l.Sublist out
  | 0, _, _, h, _, _ => by cases h
  | n + 1, ls, out, h, l, hl => by
    unfold Env.merge at h
    simp only at h
    split at h
    · rename_i he
      cases h
      have : l = [] := by
        apply Classical.byContradiction
        intro hne
        have hm : l ∈ ls.filter (· ≠ []) := List.mem_filter.mpr ⟨hl, by simpa only [ne_eq, decide_eq_true_eq] using hne⟩
        rw [List.isEmpty_iff.mp he] at hm
        cases hm
      subst this
      exact List.Sublist.slnil
    · split at h
      · cases h
      · rename_i hd hf
        cases ho : Env.merge n ((ls.filter (· ≠ [])).map fun l => l.filter (· ≠ hd)) with
        | none => rw [ho] at h; cases h
        | some out' =>
          rw [ho] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          by_cases hne : l = []
          · subst hne; exact List.nil_sublist _
          have hl' : l ∈ ls.filter (· ≠ []) := List.mem_filter.mpr ⟨hl, by simpa only [ne_eq, decide_eq_true_eq] using hne⟩
          obtain ⟨_, hnot⟩ := merge_head hf
          have ht := hnot l hl'
          have hsub := merge_sublist n _ out' ho (l.filter (· ≠ hd)) (List.mem_map.mpr ⟨l, hl', rfl⟩)
          by_cases hin : hd ∈ l
          · have hh : l.head? = Option.some hd := by
              cases l with
              | nil => cases hin
              | cons a t =>
                rcases List.mem_cons.mp hin with e | e
                · subst e; rfl
                · simp only [List.drop_one, List.tail_cons] at ht; exact absurd e ht
            rw [(filter_head ht).1 hh]
            exact hsub.cons₂ hd
          · rw [← (filter_head ht).2 hin]
            exact hsub.cons hd

/-- The merge's output contains every input element. -/
theorem merge_contains {n : Nat} {ls : List (List String)} {out : List String}
    (h : Env.merge n ls = Option.some out) : ∀ l, l ∈ ls → ∀ x, x ∈ l → x ∈ out :=
  fun l hl _ hx => (merge_sublist n ls out h l hl).subset hx

theorem mapM_spec {f : String → Option (List String)} :
    ∀ {bs : List String} {Ls : List (List String)}, bs.mapM f = Option.some Ls →
      Ls.length = bs.length ∧ ∀ (i : Nat) b Lb, bs[i]? = Option.some b → Ls[i]? = Option.some Lb → f b = Option.some Lb
  | [], Ls, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i b Lb hb _ => by simp only [List.getElem?_nil, reduceCtorEq] at hb⟩
  | b :: bs, Ls, h => by
    simp only [List.mapM_cons, bind, pure] at h
    cases hb : f b with
    | none => rw [hb] at h; cases h
    | some Lb =>
      rw [hb] at h
      simp only [Option.bind_some] at h
      cases hr : bs.mapM f with
      | none => rw [hr] at h; cases h
      | some Ls' =>
        rw [hr] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hpt⟩ := mapM_spec hr
        refine ⟨by simp only [List.length_cons, hlen], fun i b' Lb' h1 h2 => ?_⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
          subst h1 h2; exact hb
        | succ i => exact hpt i b' Lb' h1 h2

/-- **S01's C3 linearization is C3-consistent.** -/
theorem linearizeF_sound {E : Env} : ∀ (n : Nat) (c : String) (L : List String),
    E.linearizeF n c = Option.some L → C3Lin E c L
  | 0, _, _, h => by cases h
  | n + 1, c, L, h => by
    unfold Env.linearizeF at h
    simp only at h
    split at h
    · cases h
    · rename_i Ls hLs
      cases hm : Env.merge (E.decls.length * E.decls.length + 2) (Ls ++ [(E.bases c).reverse]) with
      | none => rw [hm] at h; cases h
      | some M =>
        rw [hm] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hpt⟩ := mapM_spec hLs
        exact .mk hlen (fun i b Lb hb hLb => linearizeF_sound n b Lb (hpt i b Lb hb hLb))
          (merge_nodup _ _ M hm) (merge_sublist _ _ M hm) (merge_sub _ _ M hm)

theorem linearize_sound {E : Env} {c : String} {L : List String} (h : E.linearize c = Option.some L) :
    C3Lin E c L := linearizeF_sound _ c L h

/-- In a C3 linearization every direct base comes after the contract. -/
theorem _root_.Solidity.Source.C3Lin.bases_mem {E : Env} {c : String} {L : List String} (h : C3Lin E c L) :
    ∀ b, b ∈ E.bases c → b ∈ L.drop 1 := by
  cases h with
  | mk _ _ _ hsub _ =>
    intro b hb
    exact (hsub _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))).subset (List.mem_reverse.mpr hb)

/-- **Constructor order**: the constructor order ends with the contract and
runs every direct base before it. -/
theorem ctorOrder_spec {E : Env} {c : String} {L : List String} (h : E.linearize c = Option.some L) :
    E.ctorOrder c = L.reverse ∧ (L.reverse.getLast? = Option.some c) ∧
      ∀ b, b ∈ E.bases c → b ∈ L.reverse.dropLast := by
  have hs := linearize_sound h
  have hc : E.chain c = L := by simp only [Env.chain, h, Option.getD_some]
  refine ⟨by simp only [Env.ctorOrder, hc], ?_, fun b hb => ?_⟩
  · cases hs with
    | mk _ _ _ _ _ => simp only [List.reverse_cons, List.getLast?_append, List.getLast?_singleton,
        Option.some_or]
  · have hm := hs.bases_mem b hb
    cases hs with
    | mk _ _ _ _ _ =>
      simp only [List.drop_one, List.tail_cons] at hm
      simp only [List.reverse_cons, List.dropLast_concat]
      exact List.mem_reverse.mpr hm

end Solidity.Frontend.Static
