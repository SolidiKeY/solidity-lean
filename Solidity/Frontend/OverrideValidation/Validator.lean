import Solidity.Frontend.OverrideValidation.Selection
import Solidity.Frontend.OverrideValidation.Extraction

/-!
# Additive independent G14 override graph validator

The input is one existing resolved Source Env. This candidate does not replace
InheritanceOK/inheritanceB or G15 admission. It validates original declarations
and graph edges, then supplies original-identity implementation selections.
G13 expression/body typing, constructor arguments and using-for resolution stay
at their existing boundaries; no compiler parity for those is claimed here.
-/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

structure OverrideGraphOK (E : Env) : Prop where
  extraction : ExtractionOK E
  valid : GraphValid E
  memberNames : ∀ c : Node E, contractB c.decl = true → MemberNames E c
  inheritedFamilies : ∀ c : Node E, contractB c.decl = true → InheritedFamilies E c
  overrides : ∀ c : Node E, contractB c.decl = true → ∀ d : Node E,
    (family d.decl).isSome = true → Own E c d → DeclarationOverrides E c d
  ambiguity : ∀ c : Node E, contractB c.decl = true → ∀ key : Node E,
    (family key.decl).isSome = true → AmbiguityResolved E c key
  implementation : ∀ c : Node E, contractB c.decl = true → ∀ key : Node E,
    (family key.decl).isSome = true → Implemented E c key

def validateB (E : Env) : Bool :=
  extractionB E && graphValidB E && (nodes E).all fun c => !contractB c.decl ||
    (memberNamesB E c && inheritedFamiliesB E c) && (nodes E).all fun key => !(family key.decl).isSome ||
      ((!ownB E c key || declarationOverridesB E c key) && ambiguityB E c key && implementationB E c key)

theorem validateB_iff {E : Env} : validateB E = true ↔ OverrideGraphOK E := by
  simp only [validateB, Bool.and_eq_true, extractionB_iff, graphValidB_iff, all_nodes_iff,
    Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    ownB_iff, declarationOverridesB_iff, ambiguityB_iff, implementationB_iff, inheritedFamiliesB_iff, memberNamesB_iff]
  constructor
  · rintro ⟨⟨hex, hv⟩, hc⟩
    refine ⟨hex, hv, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hco
      have hh := hc c
      grind
    · intro c hco
      have hh := hc c
      grind
    · intro c hco d hd ho
      have hh := hc c
      grind
    · intro c hco key hk
      have hh := hc c
      grind
    · intro c hco key hk
      have hh := hc c
      grind
  · intro h
    refine ⟨⟨h.extraction, h.valid⟩, ?_⟩
    intro c
    by_cases hc : contractB c.decl = true
    · right
      refine ⟨⟨h.memberNames c hc, h.inheritedFamilies c hc⟩, ?_⟩
      intro key
      by_cases hk : (family key.decl).isSome = true
      · right
        refine ⟨⟨?_, h.ambiguity c hc key hk⟩, h.implementation c hc key hk⟩
        by_cases ho : Own E c key
        · exact .inr (h.overrides c hc key hk ho)
        · exact .inl ho
      · exact .inl hk
    · exact .inl hc

/-- A certificate is indexed by the same Env whose declarations are selected. -/
structure Candidate (E : Env) : Type where
  proof : OverrideGraphOK E

def certify (E : Env) : Option (Candidate E) :=
  if h : validateB E = true then some ⟨validateB_iff.mp h⟩ else none

/-- Every successful concrete callable obligation yields an implemented
original declaration, with the independently specified selection priority. -/
theorem concrete_implemented {E : Env} (h : OverrideGraphOK E)
    {c key : Node E} (hc : contractB c.decl = true)
    (hk : (family key.decl).isSome = true) (hkind : c.decl.kind = .contract)
    (ha : E.isAbstract c.decl.name = false) (hs : HasOwn E c key ∨ HasBase E c key) :
    ∃ d, Chosen E c key d ∧ implemented d.decl = true :=
  h.implementation c hc key hk hkind ha hs

theorem accepted_no_self_base {E : Env} (h : OverrideGraphOK E) (d : Node E) : ¬ BaseEdge E d d :=
  valid_no_self_base h.valid d

theorem accepted_owner_identity {E : Env} (h : OverrideGraphOK E) {a b : Node E}
    (ha : topOwnerB a.decl = true) (hb : topOwnerB b.decl = true)
    (hn : a.decl.name = b.decl.name) : a = b := h.valid.uniqueOwners a b ha hb hn

theorem accepted_slot_identity {E : Env} (h : OverrideGraphOK E) {c a b : Node E}
    (ha : Own E c a) (hb : Own E c b) (hs : SameSlot E a.decl b.decl) : a = b :=
  h.valid.uniqueSlots c a b ha hb hs

theorem certify_isSome_iff {E : Env} : (certify E).isSome = true ↔ OverrideGraphOK E := by
  unfold certify
  split
  · rename_i h
    exact ⟨fun _ => validateB_iff.mp h, fun _ => rfl⟩
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact (h (validateB_iff.mpr he)).elim

theorem certify_none_iff {E : Env} : certify E = none ↔ ¬ OverrideGraphOK E := by
  constructor
  · intro hn hg
    have hs : (certify E).isSome = true := certify_isSome_iff.mpr hg
    rw [hn] at hs
    cases hs
  · intro hg
    cases h : certify E with
    | none => rfl
    | some candidate => exact (hg candidate.proof).elim

/-- Exact extraction prevents omitting or substituting a root's declaration body. -/
theorem accepted_collected_member {E : Env} (h : OverrideGraphOK E)
    {root d : Decl} (hr : root ∈ rootDeclarations E) (hd : d ∈ root.node.collect none) :
    ∃ n : Node E, n.decl = d := collected_member_position h.extraction hr hd

end Solidity.Frontend.OverrideValidation
