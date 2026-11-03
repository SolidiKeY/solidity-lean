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

/-- Routine derivation-field transport; no witness/proof supplied here. -/
abbrev DerivedModifierMembership : Prop :=
  ∀ (E : Env) (host : Decl) (frame : Frame) (Γ : RCtx) (m : RModInv E Γ),
    RModInv.Derived E host frame m → m.modifier ∈ E.decls

/-- Routine filter transport for actual external overloads; no proof supplied. -/
abbrev ExternalOverloadMembership : Prop :=
  ∀ (E : Env) (B : DeclName → DeclName → Bool) (target : DeclName)
    (name : String) (args : List STy) (d : Decl),
    d ∈ extOverloads E B target name args → d ∈ E.decls

/-- info: 'Solidity.Frontend.Admission.ModifierRoots.modifier_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms modifier_registered
end Solidity.Frontend.Admission.ModifierRoots
