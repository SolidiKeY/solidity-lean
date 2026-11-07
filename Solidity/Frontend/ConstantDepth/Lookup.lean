import Solidity.Frontend.ConstantDepth.Rank

/-! # Lookup identities for the existing declaration graph

The no-clash premise below is an internal projection of the existing
well-formed resolved-unit contract, not a replacement resolution check.
-/
namespace Solidity.Frontend.ConstantDepth
open Solidity.Source Solidity.Frontend.Static

theorem declared_identity {E : Env} {s : Option String} {x : String} {d : Decl}
    (hd : d ∈ E.declared s x) : d.scope = s ∧ d.name = x ∧ x ≠ "" := by
  have hp := (List.mem_filter.mp hd).2
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem lookup_identity {E : Env} {s : Option String} {x : String} {d : Decl}
    (hd : d ∈ E.lookup s x) : d.name = x ∧ x ≠ "" := by
  unfold Env.lookup at hd
  simp only at hd
  split at hd
  · have hi := declared_identity (List.mem_filter.mp hd).1
    exact ⟨hi.2.1, hi.2.2⟩
  · have hi := declared_identity hd
    exact ⟨hi.2.1, hi.2.2⟩

theorem constant_not_overload {d : Decl} (hc : d.isConst = true) :
    d.kind ≠ .function ∧ d.kind ≠ .event := by
  constructor
  · intro hk
    cases d with
    | mk k name scope top node =>
      cases hk
      cases hc
  · intro hk
    cases d with
    | mk k name scope top node =>
      cases hk
      cases hc

/-- Any same-scope, same-name pair involving a constant clashes. -/
theorem constant_clash {E : Env} {a b : Decl}
    (hc : a.isConst = true ∨ b.isConst = true)
    (hn : a.name = b.name) (hs : a.scope = b.scope) (hne : a.name ≠ "") :
    a.clash E b = true := by
  have hf : ¬ (a.kind == .function && b.kind == .function) = true := by
    intro h
    have h' := Bool.and_eq_true_iff.mp h
    rcases hc with hc | hc
    · exact (constant_not_overload hc).1 (beq_iff_eq.mp h'.1)
    · exact (constant_not_overload hc).1 (beq_iff_eq.mp h'.2)
  have he : ¬ (a.kind == .event && b.kind == .event) = true := by
    intro h
    have h' := Bool.and_eq_true_iff.mp h
    rcases hc with hc | hc
    · exact (constant_not_overload hc).2 (beq_iff_eq.mp h'.1)
    · exact (constant_not_overload hc).2 (beq_iff_eq.mp h'.2)
  unfold Decl.clash
  apply Bool.or_eq_true_iff.mpr
  right
  rw [if_neg hf, if_neg he]
  simp only [Bool.and_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  exact ⟨⟨hne, hn⟩, hs⟩

/-- A pairwise list with a member incompatible in either direction is a singleton. -/
theorem singleton_of_pairwise {α : Type} {R : α → α → Prop} {a : α} {L : List α}
    (hp : L.Pairwise R) (ha : a ∈ L)
    (hn : ∀ b ∈ L, ¬ R a b ∧ ¬ R b a) : L = [a] := by
  induction L with
  | nil => cases ha
  | cons b L ih =>
    have hp' := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp ha with rfl | ha
    · cases L with
      | nil => rfl
      | cons c L =>
        exact False.elim ((hn c (List.mem_cons_of_mem _ List.mem_cons_self)).1
          (hp'.1 c List.mem_cons_self))
    · exact False.elim ((hn b List.mem_cons_self).2 (hp'.1 a ha))

/-- Existing no-clash well-formedness forces a constant's declared set to be singleton. -/
theorem declared_constant_singleton {E : Env} {s : Option String} {x : String} {d : Decl}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false)
    (hd : d ∈ E.declared s x) (hc : d.isConst = true) : E.declared s x = [d] := by
  apply singleton_of_pairwise (hw.filter _) hd
  intro b hb
  have hi := declared_identity hd
  have hj := declared_identity hb
  have hn : d.name = b.name := hi.2.1.trans hj.2.1.symm
  have hs : d.scope = b.scope := hi.1.trans hj.1.symm
  have hne : d.name ≠ "" := by rw [hi.2.1]; exact hi.2.2
  have hde := constant_clash (E := E) (.inl hc) hn hs hne
  have hbd := constant_clash (E := E) (.inr hc) hn.symm hs.symm (by rw [← hn]; exact hne)
  constructor <;> intro h <;> first
    | (rw [h] at hde; cases hde)
    | (rw [h] at hbd; cases hbd)

/-- The initializer scope's linearization starts at that scope, even on fallback. -/
theorem linearize_starts (E : Env) (c : String) :
    ∃ tail, (E.linearize c).getD [c] = c :: tail := by
  unfold Env.linearize
  simp only [Env.linearizeF]
  cases hm : (E.bases c).reverse.mapM (E.linearizeF E.decls.length) with
  | none => exact ⟨[], rfl⟩
  | some ls =>
    simp only
    cases hm' : Env.merge (E.decls.length * E.decls.length + 2) (ls ++ [(E.bases c).reverse]) with
    | none => exact ⟨[], rfl⟩
    | some tail => exact ⟨tail, rfl⟩

/-- Lookup from a declaration's own scope retains its singleton declared set. -/
theorem lookup_own_singleton {E : Env} {s : Option String} {x : String} {d : Decl}
    (hd : E.declared s x = [d]) : E.lookup s x = [d] := by
  cases s with
  | none => exact hd
  | some c =>
    obtain ⟨tail, ht⟩ := linearize_starts E c
    have hv : E.visible (some c) (some c) x = [d] := by
      simp only [Env.visible, beq_self_eq_true, Bool.true_or, hd, List.filter_cons, List.filter_nil, ↓reduceIte]
    unfold Env.lookup
    simp only
    rw [ht]
    simp only [List.map_cons, List.find?_cons, hv, List.isEmpty_cons, Bool.not_false]

/-- A resolved constant normalizes to the identical declaration in its own scope. -/
theorem lookup_constant_canonical {E : Env} {s : Option String} {x : String} {d : Decl}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false)
    (hl : E.lookup s x = [d]) (hc : d.isConst = true) :
    E.lookup d.scope d.name = [d] := by
  have hd : d ∈ E.lookup s x := by rw [hl]; exact List.mem_cons_self
  have hi := lookup_identity hd
  apply lookup_own_singleton
  apply declared_constant_singleton hw
  · apply List.mem_filter.mpr
    exact ⟨Env.lookup_sub hd, by simpa only [beq_self_eq_true, Bool.true_and, hi.1, bne_iff_ne] using hi.2⟩
  · exact hc

/-- Every actually resolved named occurrence of an initializer is an old graph edge. -/
theorem initializer_dependency {E : Env} {s : Option String} {x y : String} {d d' : Decl}
    {e : Syn .expr} (hw : E.decls.Pairwise fun a b => a.clash E b = false)
    (hl : E.lookup s x = [d]) (hc : d.isConst = true) (he : d.init? = some e)
    (hp : (⟨y, []⟩ : IdPath) ∈ e.paths) (hy : E.lookup d.scope y = [d']) (hc' : d'.isConst = true) :
    (d'.scope, d'.name) ∈ E.constDeps (d.scope, d.name) :=
  mem_constDeps_iff.mpr ⟨d, e, ⟨y, []⟩, d', lookup_constant_canonical hw hl hc,
    hc, he, hp, hy, hc', rfl⟩

/-- The finite rank decreases on each actually resolved initializer reference. -/
theorem rank_resolved_dependency_lt {E : Env} {s : Option String} {x y : String} {d d' : Decl}
    {e : Syn .expr} (hw : E.decls.Pairwise fun a b => a.clash E b = false)
    (ha : ConstsAcyclic E) (hl : E.lookup s x = [d]) (hc : d.isConst = true)
    (he : d.init? = some e) (hp : (⟨y, []⟩ : IdPath) ∈ e.paths)
    (hy : E.lookup d.scope y = [d']) (hc' : d'.isConst = true) :
    rank E (d'.scope, d'.name) < rank E (d.scope, d.name) := by
  apply rank_lt ha
  · apply mem_constNodes_iff.mpr
    exact ⟨d, Env.lookup_sub (by rw [hl]; exact List.mem_cons_self), hc, rfl⟩
  · exact initializer_dependency hw hl hc he hp hy hc'

end Solidity.Frontend.ConstantDepth
