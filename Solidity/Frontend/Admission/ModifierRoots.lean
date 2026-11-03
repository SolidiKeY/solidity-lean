import Solidity.Frontend.Admission.NameResolutionRoots
import Solidity.Source.Elaborated

/-! Initial modifier target registration from the actual Source selector.
No dispatch, complete execution-root or SourceSpec inhabitant is supplied. -/
namespace Solidity.Frontend.Admission.ModifierRoots
open Solidity.Source
open NameResolutionRoots
theorem modifier_registered {E : Env} {scope : Option String} {path : IdPath}
    {d : Decl} {ps : List STy} (h : E.modifierAt scope path = some (d, ps)) :
    d ∈ E.decls := by
  unfold Env.modifierAt at h
  split at h
  · rename_i m hp
    have hm : m ∈ E.decls := path_registered E scope path m
      (by rw [hp]; exact List.mem_singleton_self m)
    split at h
    · obtain ⟨types, _, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      exact hm
    · cases h
      exact hm
    · cases h
  · cases h

/-- Actual derivation-field transport, proved below. -/
abbrev DerivedModifierMembership : Prop :=
  ∀ (E : Env) (host : Decl) (frame : Frame) (Γ : RCtx) (m : RModInv E Γ),
    RModInv.Derived E host frame m → m.modifier ∈ E.decls

/-- Actual external-overload registration, proved below. -/
abbrev ExternalOverloadMembership : Prop :=
  ∀ (E : Env) (B : DeclName → DeclName → Bool) (target : DeclName)
    (name : String) (args : List STy) (d : Decl),
    d ∈ extOverloads E B target name args → d ∈ E.decls

/-- info: 'Solidity.Frontend.Admission.ModifierRoots.modifier_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms modifier_registered
theorem derived_modifier_membership : Solidity.Frontend.Admission.ModifierRoots.DerivedModifierMembership := by
  intro E host frame Γ m h
  obtain ⟨p, a, es, _, hs, _, _⟩ := h
  exact Solidity.Frontend.Admission.ModifierRoots.modifier_registered hs

/-- info: 'Solidity.Frontend.Admission.ModifierRoots.derived_modifier_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms derived_modifier_membership
theorem external_overload_membership : Solidity.Frontend.Admission.ModifierRoots.ExternalOverloadMembership := by
  intro E B target name args d h
  unfold Solidity.Source.extOverloads Solidity.Source.Env.extFunctions at h
  exact Solidity.Frontend.Admission.NameResolutionRoots.lookup_registered E (some target.name) name d
    ((List.mem_filter.mp (List.mem_filter.mp h).1).1)

/-- info: 'Solidity.Frontend.Admission.ModifierRoots.external_overload_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms external_overload_membership
end Solidity.Frontend.Admission.ModifierRoots
