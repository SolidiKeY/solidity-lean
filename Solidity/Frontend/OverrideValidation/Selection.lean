import Solidity.Frontend.OverrideValidation.Validity

/-! Implementation selection retains the requested and chosen original
positions. Source's checked C3 order is a lower-stage input; graph validity
requires successful linearization, so its fallback chain is not admitted. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

/-- A visible declaration at a particular position in the C3 scope order. -/
def Exposes (E : Env) (c key : Node E) (scope : String) (d : Node E) : Prop :=
  d.decl.scope = some scope ∧ SameSlot E key.decl d.decl ∧
    (scope = c.decl.name ∨ d.decl.isPrivate = false)

def exposesB (E : Env) (c key : Node E) (scope : String) (d : Node E) : Bool :=
  d.decl.scope == some scope && sameSlotB E key.decl d.decl &&
    (scope == c.decl.name || !d.decl.isPrivate)

def scopeChoice (E : Env) (c key : Node E) (scope : String) : Option (Node E) :=
  (nodes E).find? (exposesB E c key scope)

/-- First matching original declaration in a scope; the prefix formulation
also specifies deterministic behavior on malformed inputs, later rejected. -/
def FirstInScope (E : Env) (c key : Node E) (scope : String) (d : Node E) : Prop :=
  Exposes E c key scope d ∧ ∃ before after, nodes E = before ++ d :: after ∧
    ∀ f ∈ before, ¬ Exposes E c key scope f

/-- The first scope with a matching declaration, preserving its position. -/
def Chosen (E : Env) (c key d : Node E) : Prop :=
  ∃ before scope after, E.chain c.decl.name = before ++ scope :: after ∧
    FirstInScope E c key scope d ∧ ∀ prior ∈ before, ∀ f, ¬ Exposes E c key prior f

def choose (E : Env) (c key : Node E) : Option (Node E) :=
  (E.chain c.decl.name).findSome? (scopeChoice E c key)

/-- Successful selection returns both original declaration identities. -/
def dispatch (E : Env) (c key : Node E) : Option (Selection E) :=
  (choose E c key).map fun d => ⟨key, d⟩

def HasOwn (E : Env) (c key : Node E) : Prop :=
  ∃ d, Own E c d ∧ SameSlot E key.decl d.decl

def hasOwnB (E : Env) (c key : Node E) : Bool :=
  (nodes E).any fun d => ownB E c d && sameSlotB E key.decl d.decl

/-- A concrete contract implements every own or inherited callable slot. -/
def Implemented (E : Env) (c key : Node E) : Prop :=
  c.decl.kind = .contract → E.isAbstract c.decl.name = false →
    (HasOwn E c key ∨ HasBase E c key) → ∃ d, Chosen E c key d ∧ implemented d.decl = true

def implementationB (E : Env) (c key : Node E) : Bool :=
  c.decl.kind != .contract || E.isAbstract c.decl.name ||
    !(hasOwnB E c key || hasBaseB E c key) ||
      match choose E c key with
      | none => false
      | some d => implemented d.decl

/-- Multiple retained implementations require a local declaration. -/
def AmbiguityResolved (E : Env) (c key : Node E) : Prop :=
  HasOwn E c key ∨ ¬ ∃ f g, Retained E c key f ∧ Retained E c key g ∧ f ≠ g

def ambiguityB (E : Env) (c key : Node E) : Bool :=
  hasOwnB E c key || !((nodes E).any fun f => retainedB E c key f &&
    (nodes E).any fun g => retainedB E c key g && f != g)

theorem exposesB_iff {E : Env} {c key d : Node E} {scope : String} :
    exposesB E c key scope d = true ↔ Exposes E c key scope d := by
  simp only [exposesB, Exposes, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, sameSlotB_iff, and_assoc]

theorem scopeChoice_iff {E : Env} {c key d : Node E} {scope : String} :
    scopeChoice E c key scope = some d ↔ FirstInScope E c key scope d := by
  simp only [scopeChoice, FirstInScope, List.find?_eq_some_iff_append,
    exposesB_iff, Bool.not_eq_true', Bool.eq_false_iff, ne_eq]

theorem scopeChoice_none_iff {E : Env} {c key : Node E} {scope : String} :
    scopeChoice E c key scope = none ↔ ∀ d, ¬ Exposes E c key scope d := by
  simp only [scopeChoice, List.find?_eq_none, mem_nodes, true_implies, exposesB_iff]

theorem choose_iff {E : Env} {c key d : Node E} : choose E c key = some d ↔ Chosen E c key d := by
  simp only [choose, Chosen, List.findSome?_eq_some_iff, scopeChoice_iff, scopeChoice_none_iff]

theorem chosen_unique {E : Env} {c key a b : Node E}
    (ha : Chosen E c key a) (hb : Chosen E c key b) : a = b :=
  Option.some.inj ((choose_iff.mpr ha).symm.trans (choose_iff.mpr hb))

theorem chosen_slot {E : Env} {c key d : Node E} (h : Chosen E c key d) : SameSlot E key.decl d.decl := by
  obtain ⟨_, _, _, _, hfirst, _⟩ := h
  exact hfirst.1.2.1

theorem hasOwnB_iff {E : Env} {c key : Node E} : hasOwnB E c key = true ↔ HasOwn E c key := by
  simp only [hasOwnB, HasOwn, any_nodes_iff, Bool.and_eq_true, ownB_iff, sameSlotB_iff]

theorem implementationB_iff {E : Env} {c key : Node E} :
    implementationB E c key = true ↔ Implemented E c key := by
  have hc : (match choose E c key with | none => false | some d => implemented d.decl) = true ↔
      ∃ d, Chosen E c key d ∧ implemented d.decl = true := by
    cases h : choose E c key with
    | none =>
      simp only [Bool.false_eq_true]
      constructor
      · intro he
        cases he
      · rintro ⟨d, hd, _⟩
        have he := choose_iff.mpr hd
        rw [h] at he
        cases he
    | some d =>
      constructor
      · intro hi
        exact ⟨d, choose_iff.mp h, hi⟩
      · rintro ⟨f, hf, hi⟩
        have he : d = f := Option.some.inj (h.symm.trans (choose_iff.mpr hf))
        exact he.symm ▸ hi
  simp only [implementationB, Implemented, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, Bool.eq_false_iff, ne_eq, hasOwnB_iff, hasBaseB_iff, hc]
  grind

theorem ambiguityB_iff {E : Env} {c key : Node E} :
    ambiguityB E c key = true ↔ AmbiguityResolved E c key := by
  simp only [ambiguityB, AmbiguityResolved, Bool.or_eq_true, hasOwnB_iff,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, any_nodes_iff, Bool.and_eq_true,
    retainedB_iff, bne_iff_ne]
  grind

theorem dispatch_iff {E : Env} {c key : Node E} {selected : Selection E} :
    dispatch E c key = some selected ↔ selected.requested = key ∧ Chosen E c key selected.chosen := by
  obtain ⟨requested, chosen⟩ := selected
  simp only [dispatch, Option.map_eq_some_iff, choose_iff, Selection.mk.injEq]
  constructor
  · rintro ⟨f, hf, hk, he⟩
    cases he
    exact ⟨hk.symm, hf⟩
  · rintro ⟨hk, hf⟩
    exact ⟨chosen, hf, hk.symm, rfl⟩

theorem dispatch_original {E : Env} {c key : Node E} {selected : Selection E}
    (h : dispatch E c key = some selected) :
    selected.requested = key ∧ E.decls[selected.chosen.val]? = some selected.chosen.decl ∧
      SameSlot E key.decl selected.chosen.decl := by
  obtain ⟨hk, hd⟩ := dispatch_iff.mp h
  exact ⟨hk, selected_lookup selected, chosen_slot hd⟩

end Solidity.Frontend.OverrideValidation
