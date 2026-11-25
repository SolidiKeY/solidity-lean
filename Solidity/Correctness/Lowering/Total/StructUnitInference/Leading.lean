import Solidity.Correctness.Lowering.Total.StructUnit
import Solidity.Correctness.Lowering.Total.CalleeInference

/-!
# The leading declarations of an assembled mixed unit

The leading parts `appendParts ss p` of a successful `StructUnit.build` (`ss` from
`StructDecode.decode`, `p` from `prefixParts`) are structs, the constructor or state roots
of the contract scope (`leading_kind`): no function (`leading_noFunction`), so
`PrefixRejects` holds for every name and context (`leading_prefixRejects`) while those
names may still coincide with callable ones. The only file-level declaration is the
contract (`build_declared_none`).
-/
namespace Solidity.Correctness.Lowering.Total.StructUnitInference

open Source (Syn)
open Decode Decode.Callee CalleeResolution CalleeSelection
open StructUnit (build build_ok build_decls gen_kind collect_append)
open ReferenceStatePlacement (prefixParts prefixParts_collect state_kind ctorDecls_kind)

variable {T : Tables} {R : CallSpellExt.Registry} {C : Contract} {scope : String}
  {fs : List (Name × FunDecl)} {u : Syn .unit} {ss p : Syn (.list (.part false))}

/-- **Leading kinds**: every leading declaration is a struct, the constructor or a
state root, declared in the contract scope. -/
theorem leading_kind (hs : StructDecode.decode C = .ok ss) (hp : prefixParts T R C = .ok p) :
    ∀ d ∈ (appendParts ss p).collect (some scope),
      (d.kind = .struct ∨ d.kind = .constructor ∨ d.kind = .stateVar) ∧
        d.scope = some scope := by
  intro d hd
  rw [collect_append] at hd
  obtain ⟨st, ctors, hst, hc, hcol⟩ := prefixParts_collect hp scope
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨k, s⟩ := gen_kind hs hd; exact ⟨.inl k, s⟩
  · rw [hcol] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k, s⟩ := ctorDecls_kind hc d hd; exact ⟨.inr (.inl k), s⟩
    · obtain ⟨k, s, _⟩ := state_kind hst scope d hd; exact ⟨.inr (.inr k), s⟩

/-- No leading declaration is a function. -/
theorem leading_noFunction (hs : StructDecode.decode C = .ok ss)
    (hp : prefixParts T R C = .ok p) :
    ∀ d ∈ (appendParts ss p).collect (some scope), d.kind ≠ .function := by
  intro d hd hk
  rcases (leading_kind hs hp d hd).1 with k | k | k <;> rw [hk] at k <;> cases k

/-- **Prefix rejection, derived**: the actual leading prefix rejects every call, by kind. -/
theorem leading_prefixRejects (hs : StructDecode.decode C = .ok ss)
    (hp : prefixParts T R C = .ok p) (Γ : Source.Ctx) (σs : List Source.STy) (x : String) :
    PrefixRejects Γ σs scope (appendParts ss p) x :=
  fun d hd => .inl (leading_noFunction hs hp d (List.mem_filter.mp hd).1)

/-- No prefix declaration of any name is a callable function. -/
theorem leading_functions_nil (hs : StructDecode.decode C = .ok ss)
    (hp : prefixParts T R C = .ok p) (x : String) :
    (prefixNamed scope (appendParts ss p) x).filter
      (fun d => d.kind == .function && d.callableFrom (some scope)) = [] :=
  List.filter_eq_nil_iff.mpr fun d hd => by
    simp [leading_noFunction hs hp d (List.mem_filter.mp hd).1]

/-- The translated functions are declared in the contract scope. -/
theorem functions_inScope {functions : Syn (.list (.part false))}
    (hf : functionParts T R scope fs = some functions) :
    ∀ d ∈ functions.collect (some scope), d.scope = some scope := by
  intro d hm
  have : some d ∈ fs.map (fun f => fromMetadata T R scope f.2) := by
    rw [← functionParts_faithful T R scope fs functions hf]; exact List.mem_map_of_mem hm
  obtain ⟨e, _, he⟩ := List.mem_map.mp this
  obtain ⟨_, _, _, _, _, _, hsc⟩ := fromMetadata_header he
  exact hsc

/-- The only file-level declaration of the unit is the contract. -/
theorem build_declared_none (h : build T R C scope fs = .ok u) {x : String} :
    ∀ d ∈ u.env.declared none x, d.kind = .contract := by
  obtain ⟨k, ss, st, ctors, functions, hk, -, hs, hst, hc, hf, hd, -, -⟩ := build_decls h
  obtain ⟨_, p, -, hp, -⟩ := build_ok h
  intro d hm
  obtain ⟨hm, hq⟩ := List.mem_filter.mp hm
  have hn : d.scope = none := by simp at hq; exact hq.1.1
  rw [hd] at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hk
  · exfalso
    have : d.scope = some scope := by
      simp only [List.mem_append] at hm
      rcases hm with (hm | hm | hm) | hm
      · exact (gen_kind hs hm).2
      · exact (ctorDecls_kind hc d hm).2
      · exact (state_kind hst scope d hm).2.1
      · exact functions_inScope hf d hm
    rw [hn] at this; cases this

end Solidity.Correctness.Lowering.Total.StructUnitInference
