import Solidity.Source.Typing

/-! Initial target membership derived from the actual source name resolver.
No assumptions about arbitrary constructed RExpr targets or runtime receiver
rosters are introduced. -/
namespace Solidity.Frontend.Admission.NameResolutionRoots
open Solidity.Source

theorem lookup_registered (E : Env) (scope : Option String) (name : String) (d : Decl)
    (h : d ∈ E.lookup scope name) : d ∈ E.decls := by
  cases scope with
  | none =>
    simp only [Env.lookup, List.find?_nil, Env.declared, List.mem_filter] at h
    exact h.1
  | some c =>
    cases hf : (((E.linearize c).getD [c]).map Option.some).find?
        (fun s => !(E.visible (some c) s name).isEmpty) with
    | none =>
      simp only [Env.lookup, hf, Env.declared, List.mem_filter] at h
      exact h.1
    | some found =>
      simp only [Env.lookup] at h
      rw [hf] at h
      simp only [Env.visible, Env.declared, List.mem_filter] at h
      exact h.1.1

theorem resolved_registered {E : Env} {locals : List String} {scope : Option String}
    {name : String} {ds : List Decl} {d : Decl}
    (hr : E.resolve locals scope name = some (.decls ds)) (hd : d ∈ ds) :
    d ∈ E.decls := by
  cases Env.resolve_sound hr with
  | decl hlocal hlookup => exact lookup_registered E scope name d hd

theorem functions_registered {Γ : Ctx} {name : String} {d : Decl}
    (h : d ∈ Γ.functions name) : d ∈ Γ.env.decls := by
  unfold Ctx.functions at h
  split at h
  · rename_i ds hr
    exact resolved_registered hr (List.mem_filter.mp h).1
  · cases h

theorem path_registered (E : Env) (scope : Option String) (path : IdPath) (d : Decl)
    (h : d ∈ E.lookupPath scope path) : d ∈ E.decls := by
  unfold Env.lookupPath at h
  split at h
  · exact lookup_registered E scope path.head d h
  · simp only [Env.declared, List.mem_filter] at h
    exact h.1
  · cases h

/-- Routine selected-overload corollary to be supplied by Terra; no proof is
exported. This is the singleton-selection field of the source call rule. -/
abbrev SelectedFunctionMembership : Prop :=
  ∀ (Γ : Ctx) (name : String) (filter : Decl → Bool) (d : Decl),
    (Γ.functions name).filter filter = [d] → d ∈ Γ.env.decls

/-- info: 'Solidity.Frontend.Admission.NameResolutionRoots.path_registered' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms path_registered

/-- info: 'Solidity.Frontend.Admission.NameResolutionRoots.functions_registered' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms functions_registered
/-- info: 'Solidity.Frontend.Admission.NameResolutionRoots.resolved_registered' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_registered
/-- info: 'Solidity.Frontend.Admission.NameResolutionRoots.lookup_registered' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms lookup_registered
end Solidity.Frontend.Admission.NameResolutionRoots
