import Solidity.Frontend.Static.Consts

/-!
# Finite ranks for the existing named-constant graph

No declarations are deduplicated and no lookup is replaced. The rank counts
entries of `constNodes` reachable from a node, including the node itself.
Duplicate entries can increase the rank, but cannot exceed the declaration
count. Acyclicity makes each dependency remove at least the parent entry.
-/

namespace Solidity.Frontend.ConstantDepth

open Solidity.Source Solidity.Frontend.Static

abbrev Node := Option String × String

/-- The exact witnesses retained by the existing dependency extraction. -/
theorem mem_constDeps_iff {E : Env} {a b : Node} :
    b ∈ E.constDeps a ↔ ∃ d e p d',
      E.lookup a.1 a.2 = [d] ∧ d.isConst = true ∧ d.init? = some e ∧
      p ∈ e.paths ∧ E.lookupPath d.scope p = [d'] ∧ d'.isConst = true ∧
      b = (d'.scope, d'.name) := by
  unfold Env.constDeps
  split
  · rename_i d hd
    by_cases hc : d.isConst = true
    · rw [if_pos hc]
      split
      · rename_i e he
        constructor
        · intro h
          obtain ⟨p, hp, hb⟩ := List.mem_filterMap.mp h
          split at hb
          · rename_i d' hd'
            split at hb
            · rename_i hc'
              cases hb
              exact ⟨d, e, p, d', hd, hc, he, hp, hd', hc', rfl⟩
            · cases hb
          · cases hb
        · rintro ⟨d', e', p, t, hd', hc', he', hp, ht, htc, rfl⟩
          rw [hd] at hd'; cases hd'
          rw [he] at he'; cases he'
          apply List.mem_filterMap.mpr
          refine ⟨p, hp, ?_⟩
          simp only [ht, htc, ↓reduceIte]
      · rename_i he
        constructor
        · intro h; cases h
        · rintro ⟨d', e', p, t, hd', hc', he', hp, ht, htc, hb⟩
          rw [hd] at hd'; cases hd'
          rw [he] at he'; cases he'
    · rw [if_neg hc]
      constructor
      · intro h; cases h
      · rintro ⟨d', e, p, t, hd', hc', rest⟩
        rw [hd] at hd'; cases hd'
        exact False.elim (hc hc')
  · rename_i hn
    constructor
    · intro h; cases h
    · rintro ⟨d, e, p, t, hd, rest⟩
      exact False.elim (hn d hd)

/-- Node membership retains a declaration witness, including duplicates. -/
theorem mem_constNodes_iff {E : Env} {a : Node} :
    a ∈ constNodes E ↔ ∃ d ∈ E.decls, d.isConst = true ∧ (d.scope, d.name) = a := by
  simp only [constNodes, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨d, ⟨hd, hc⟩, he⟩; exact ⟨d, hd, hc, he⟩
  · rintro ⟨d, hd, hc, he⟩; exact ⟨d, ⟨hd, hc⟩, he⟩

theorem constNodes_length_le (E : Env) : (constNodes E).length ≤ E.decls.length := by
  simp only [constNodes, List.length_map]
  exact List.length_filter_le _ _

/-- The pre-existing finite saturation decides reachability on graph nodes. -/
def reaches (E : Env) (a b : Node) : Bool :=
  (reachable E.constDeps (constNodes E) a).contains b

theorem reaches_iff {E : Env} {a b : Node} (ha : a ∈ constNodes E) :
    reaches E a b = true ↔ Reach E.constDeps a b := by
  simp only [reaches, List.contains_eq_mem, decide_eq_true_eq]
  exact mem_reachable (fun _ _ _ hb => constDeps_sub hb) ha

/-- A finite rank, derived from declaration membership rather than evaluation. -/
def rank (E : Env) (a : Node) : Nat :=
  ((constNodes E).filter (reaches E a)).length

theorem rank_le_decls (E : Env) (a : Node) : rank E a ≤ E.decls.length :=
  Nat.le_trans (List.length_filter_le _ _) (constNodes_length_le E)

/-- Filtering the same ledger by a smaller predicate cannot increase length. -/
theorem filter_length_mono {α : Type} (U : List α) (p q : α → Bool)
    (h : ∀ x ∈ U, p x = true → q x = true) :
    (U.filter p).length ≤ (U.filter q).length := by
  induction U with
  | nil => exact Nat.le_refl _
  | cons a U ih =>
    have hi := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    split <;> split <;> simp only [List.length_cons] at * <;> first
      | omega
      | exact False.elim (by have hq : q a = true := ha (by assumption); contradiction)

/-- A witnessed missing ledger entry makes the inequality strict. -/
theorem filter_length_strict {α : Type} (U : List α) (p q : α → Bool)
    (h : ∀ x ∈ U, p x = true → q x = true)
    (w : ∃ x ∈ U, p x = false ∧ q x = true) :
    (U.filter p).length < (U.filter q).length := by
  induction U with
  | nil => obtain ⟨x, hx, _⟩ := w; cases hx
  | cons a U ih =>
    have hm := filter_length_mono U p q (fun x hx => h x (List.mem_cons_of_mem a hx))
    obtain ⟨x, hx, hp, hq⟩ := w
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hi := ih (fun x hx => h x (List.mem_cons_of_mem a hx)) ⟨x, hx, hp, hq⟩
      have ha := h a List.mem_cons_self
      simp only [List.filter_cons]
      split <;> split <;> simp only [List.length_cons] at * <;> first
        | omega
        | exact False.elim (by have hq : q a = true := ha (by assumption); contradiction)

theorem no_self_path {E : Env} (h : ConstsAcyclic E) {a : Node}
    (ha : a ∈ constNodes E) : ¬ DepPath E a a := by
  obtain ⟨d, hd, hc, rfl⟩ := mem_constNodes_iff.mp ha
  exact h d hd hc

/-- Every actual graph dependency strictly decreases rank. -/
theorem rank_lt {E : Env} (h : ConstsAcyclic E) {a b : Node}
    (ha : a ∈ constNodes E) (hab : b ∈ E.constDeps a) : rank E b < rank E a := by
  have hb : b ∈ constNodes E := constDeps_sub hab
  apply filter_length_strict
  · intro x hx hbx
    exact (reaches_iff ha).mpr (.step hab ((reaches_iff hb).mp hbx))
  · refine ⟨a, ha, ?_, (reaches_iff ha).mpr (.refl a)⟩
    cases hr : reaches E b a with
    | false => rfl
    | true =>
      have hba := (reaches_iff hb).mp hr
      exact False.elim (no_self_path h ha (depPath_iff.mpr ⟨b, hab, hba⟩))

/-- Rank is monotone along every existing reflexive-transitive path. -/
theorem rank_mono {E : Env} {a b : Node} (ha : a ∈ constNodes E)
    (hab : Reach E.constDeps a b) : rank E b ≤ rank E a := by
  have hb : b ∈ constNodes E :=
    (Closed.reach (fun _ _ _ h => constDeps_sub h) hab ha)
  apply filter_length_mono
  intro x hx hbx
  exact (reaches_iff ha).mpr (hab.trans ((reaches_iff hb).mp hbx))

/-- Strict rank decrease extends to nonempty dependency paths. -/
theorem rank_lt_path {E : Env} (h : ConstsAcyclic E) {a b : Node}
    (ha : a ∈ constNodes E) (hab : DepPath E a b) : rank E b < rank E a := by
  obtain ⟨c, hc, hcb⟩ := depPath_iff.mp hab
  exact Nat.lt_of_le_of_lt (rank_mono (constDeps_sub hc) hcb) (rank_lt h ha hc)

/-- A graph node contributes at least its own ledger entry. -/
theorem rank_pos {E : Env} {a : Node} (ha : a ∈ constNodes E) : 0 < rank E a := by
  apply List.length_pos_of_mem
  exact List.mem_filter.mpr ⟨ha, (reaches_iff ha).mpr (.refl a)⟩

/-- A length-indexed walk in the unchanged dependency graph. -/
inductive Walk (E : Env) : Nat → Node → Node → Prop where
  | nil (a : Node) : Walk E 0 a a
  | cons {n : Nat} {a b c : Node} : b ∈ E.constDeps a → Walk E n b c → Walk E (n + 1) a c

/-- Arbitrarily long walks consume rank; no fixed-size fixture is assumed. -/
theorem walk_rank {E : Env} (h : ConstsAcyclic E) {n : Nat} {a b : Node}
    (ha : a ∈ constNodes E) (hw : Walk E n a b) : n + rank E b ≤ rank E a := by
  induction hw with
  | nil => omega
  | cons hab hw ih =>
    have hi := ih (constDeps_sub hab)
    have hs := rank_lt h ha hab
    omega

/-- Every ledger walk uses fewer edges than declarations. -/
theorem walk_length_lt_decls {E : Env} (h : ConstsAcyclic E) {n : Nat} {a b : Node}
    (ha : a ∈ constNodes E) (hw : Walk E n a b) : n < E.decls.length := by
  have hb : b ∈ constNodes E := by
    induction hw with
    | nil => exact ha
    | cons hab hw ih => exact ih (constDeps_sub hab)
  have hr := walk_rank h ha hw
  have hp := rank_pos hb
  have hl := rank_le_decls E a
  omega

end Solidity.Frontend.ConstantDepth
