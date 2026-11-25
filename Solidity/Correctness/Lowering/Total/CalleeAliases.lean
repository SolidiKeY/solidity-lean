import Solidity.Correctness.Lowering.Total.CalleeAliases.Lookup
import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Functions

/-!
# Model callee aliases and assembled Source declarations

A model callee alias is the key of an entry in the ordered `Contract.funs` list;
`Semantics.lookupBy` selects the first entry with that key. This module connects
that first match to its position (`firstIndex`), and from a successful
`Callee.withFunctions` assembly to the declaration at the same position after
the contract and the supplied prefix. That declaration carries the entry's
retained source name (not the alias) and the selected contract scope; it is the
existing `fromMetadata` translation, so `functionDecl_faithful` and
`fromFunctions_bound` supply its frame and body without a new traversal.

Boundaries proved here: lookup fails exactly when no entry has the alias;
duplicate aliases resolve to the first entry and shadow later ones; aliases are
labels the assembly ignores (`withFunctions_relabel`); an entry without retained
metadata fails the whole assembly. Successful assembly does not make source
names unique: Source name resolution of the declaration (`SourceResolves`) is an
explicit local obligation for the decoder lane, not a consequence here, and
not a premise or exclusion of `lowerLoopsCorrect`. Frame correspondence,
function-index binding, semantic callee agreement, complete-unit integration
and coverage stay with that lane; no simulation is claimed.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeAliases

open Semantics (lookupBy)
open Decode Decode.Callee

variable {T : Tables} {R : CallSpellExt.Registry} {scope : String}
  {leadingParts : Source.Syn (.list (.part false))} {fs : List (Name × FunDecl)}

/-- Position in the collected declaration table of the function entry at
`index`: after the contract declaration and the supplied prefix. -/
def entryPosition (scope : String) (leadingParts : Source.Syn (.list (.part false)))
    (index : Nat) : Nat :=
  1 + (leadingParts.collect (some scope)).length + index

/-! ## Aliases are labels -/

theorem functionParts_relabel (T : Tables) (R : CallSpellExt.Registry) (scope : String)
    (g : Name × FunDecl → Name) :
    ∀ fs : List (Name × FunDecl),
      functionParts T R scope (fs.map fun e => (g e, e.2)) = functionParts T R scope fs
  | [] => rfl
  | (_, _) :: fs => by
      simp only [List.map_cons, functionParts, functionParts_relabel T R scope g fs]

/-- Renaming model aliases leaves the assembled unit unchanged: no alias is
spelled into any declaration. -/
theorem withFunctions_relabel (g : Name × FunDecl → Name) :
    withFunctions T R scope leadingParts (fs.map fun e => (g e, e.2)) =
      withFunctions T R scope leadingParts fs := by
  simp only [withFunctions, functionParts_relabel]

/-! ## Exact assembly failure boundary -/

private theorem ordinaryNode_fromMetadata {f : FunDecl} {d : Source.Decl}
    (h : fromMetadata T R scope f = some d) : (ordinaryNode d).isSome := by
  obtain ⟨source, vis, _, _, hf, _⟩ := fromMetadata_header h
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _⟩ :=
    functionDecl_faithful T R scope source.name (some vis)
      (sourceMutability source.mutability) f d hf { decls := [] }
  rfl

theorem functionParts_isSome_iff (T : Tables) (R : CallSpellExt.Registry) (scope : String) :
    ∀ fs : List (Name × FunDecl), (functionParts T R scope fs).isSome ↔
      ∀ e ∈ fs, (fromMetadata T R scope e.2).isSome
  | [] => by simp [functionParts]
  | (a, f) :: fs => by
      rw [List.forall_mem_cons, ← functionParts_isSome_iff T R scope fs]
      cases hd : fromMetadata T R scope f with
      | none => simp [functionParts, hd]
      | some d =>
          obtain ⟨node, hn⟩ := Option.isSome_iff_exists.mp (ordinaryNode_fromMetadata hd)
          cases hr : functionParts T R scope fs <;> simp [functionParts, hd, hn, hr]

/-- Assembly succeeds exactly when every entry's retained metadata translates. -/
theorem withFunctions_isSome_iff :
    (withFunctions T R scope leadingParts fs).isSome ↔
      ∀ e ∈ fs, (fromMetadata T R scope e.2).isSome := by
  rw [← functionParts_isSome_iff]
  cases hf : functionParts T R scope fs <;> simp [withFunctions, hf]

/-- An entry without retained metadata fails the whole assembly, whatever its
alias: the alias is never used as a substitute source identity. -/
theorem withFunctions_absent {e : Name × FunDecl} (he : e ∈ fs) (hn : e.2.sourceDecl = none) :
    withFunctions T R scope leadingParts fs = none := by
  have hm : fromMetadata T R scope e.2 = none := by simp [fromMetadata, hn]
  cases hu : withFunctions T R scope leadingParts fs with
  | none => rfl
  | some u =>
      have := (withFunctions_isSome_iff (leadingParts := leadingParts)).mp (by rw [hu]; rfl) e he
      simp [hm] at this

/-! ## Positional correspondence -/

/-- The entry at `index` is translated to the declaration at its position. -/
theorem withFunctions_entry {u : Source.Syn .unit} {index : Nat} {e : Name × FunDecl}
    (h : withFunctions T R scope leadingParts fs = some u) (hi : fs[index]? = some e) :
    ∃ out, u.decls[entryPosition scope leadingParts index]? = some out ∧
      fromMetadata T R scope e.2 = some out := by
  have ht := congrArg (fun ds => ds[index]?) (withFunctions_tail h)
  simp only [List.getElem?_map, List.getElem?_drop, hi, Option.map_some] at ht
  cases hd : u.decls[1 + (leadingParts.collect (some scope)).length + index]? with
  | none => simp [hd] at ht
  | some out =>
      simp only [hd, Option.map_some, Option.some.injEq] at ht
      exact ⟨out, hd, ht.symm⟩

/-- The declaration at an entry's position has the entry's retained source
name and the selected contract scope, and is a member of the unit's table. -/
theorem withFunctions_identity {u : Source.Syn .unit} {index : Nat} {e : Name × FunDecl}
    (h : withFunctions T R scope leadingParts fs = some u) (hi : fs[index]? = some e) :
    ∃ out source, u.decls[entryPosition scope leadingParts index]? = some out ∧
      fromMetadata T R scope e.2 = some out ∧ e.2.sourceDecl = some source ∧
      out.name = source.name ∧ out.scope = some scope ∧ out ∈ u.decls := by
  obtain ⟨out, hp, hm⟩ := withFunctions_entry h hi
  obtain ⟨source, _, hs, _, _, hn, hsc⟩ := fromMetadata_header hm
  exact ⟨out, source, hp, hm, hs, hn, hsc, List.mem_of_getElem? hp⟩

/-! ## Alias lookup to declaration -/

/-- A successful alias lookup over successfully assembled entries identifies
the first entry with that alias, its position, and the declaration there,
which carries the entry's retained source name, not the alias. -/
theorem alias_entry {u : Source.Syn .unit} {a : Name} {d : FunDecl}
    (h : withFunctions T R scope leadingParts fs = some u) (hl : lookupBy a fs = some d) :
    ∃ index out source, firstIndex a fs = some index ∧ fs[index]? = some (a, d) ∧
      u.decls[entryPosition scope leadingParts index]? = some out ∧
      fromMetadata T R scope d = some out ∧ d.sourceDecl = some source ∧
      out.name = source.name ∧ out.scope = some scope ∧ out ∈ u.decls := by
  obtain ⟨index, hf, hi⟩ := lookupBy_eq_some_iff.mp hl
  obtain ⟨out, source, rest⟩ := withFunctions_identity h hi
  exact ⟨index, out, source, hf, hi, rest⟩

/-- Exact lookup failure: no entry has the alias. -/
theorem alias_none {a : Name} : lookupBy a fs = none ↔ ∀ e ∈ fs, e.1 ≠ a :=
  lookupBy_eq_none_iff.trans firstIndex_eq_none_iff

/-- Shadowing: an entry with the alias after the first match is never the
lookup result's position; distinct declarations may still sit there. -/
theorem alias_shadowed {a : Name} {index j : Nat} {d' : FunDecl}
    (hf : firstIndex a fs = some index) (hj : fs[j]? = some (a, d')) (hne : j ≠ index) :
    index < j :=
  Nat.lt_of_le_of_ne (firstIndex_le hf hj) (Ne.symm hne)

/-- Binding at the first-match position of an alias: the bound declaration is
the first aliased entry's translation, with its retained source name and the
selected scope, and the existing `fromFunctions_bound` certificate gives its
membership, elaborated resolution and body. -/
theorem fromFunctions_alias {settings : Source.Settings} {a : Name} {index : Nat}
    {s : Version.CalleeBinding.Output}
    (hf : firstIndex a fs = some index)
    (h : Version.CalleeBinding.fromFunctions T R settings scope leadingParts fs index = some s) :
    ∃ d source u, lookupBy a fs = some d ∧ fs[index]? = some (a, d) ∧
      d.sourceDecl = some source ∧ s.declaration.name = source.name ∧
      s.declaration.scope = some scope ∧
      withFunctions T R scope leadingParts fs = some u ∧
      u.decls[entryPosition scope leadingParts index]? = some s.declaration ∧
      s.source.res = Source.resolveUnit settings u ∧
      s.declaration ∈ s.source.res.env.decls ∧
      Version.CalleeBinding.fromResolution (Source.resolveUnit settings u) s.declaration =
        some s := by
  obtain ⟨d, hi⟩ := firstIndex_key hf
  obtain ⟨u, hu, hr, hm, hmem, hb⟩ := Version.CalleeBinding.fromFunctions_bound h hi
  obtain ⟨out, hp, hm'⟩ := withFunctions_entry hu hi
  obtain rfl : out = s.declaration := Option.some.inj (hm'.symm.trans hm)
  obtain ⟨source, _, hs, _, _, hn, hsc⟩ := fromMetadata_header hm
  exact ⟨d, source, u, lookupBy_eq_some_iff.mpr ⟨index, hf, hi⟩, hi, hs, hn, hsc,
    hu, hp, hr, hmem, hb⟩

/-! ## Source name resolution: an explicit obligation -/

/-- The declaration is the only one of its name declared in `scope`.
Assembly does not establish this (two entries may retain one source name);
the decoder lane must discharge it from the actual generated environment. -/
def SourceResolves (u : Source.Syn .unit) (scope : String) (out : Source.Decl) : Prop :=
  u.env.declared (some scope) out.name = [out]

/-- Without the obligation, the positional declaration is still one of the
candidates Source declares under its retained name in the selected scope. -/
theorem alias_declared {u : Source.Syn .unit} {a : Name} {d : FunDecl}
    (h : withFunctions T R scope leadingParts fs = some u) (hl : lookupBy a fs = some d) :
    ∃ out source, fromMetadata T R scope d = some out ∧ d.sourceDecl = some source ∧
      out.name = source.name ∧
      (source.name ≠ "" → out ∈ u.env.declared (some scope) source.name) := by
  obtain ⟨_, out, source, _, _, _, hm, hs, hn, hsc, hmem⟩ := alias_entry h hl
  refine ⟨out, source, hm, hs, hn, fun hne => ?_⟩
  simp only [Source.Env.declared, List.mem_filter]
  exact ⟨hmem, by simp [hsc, hn, hne]⟩

/-- Under the explicit obligation, the declaration is the unique Source
candidate for its retained name in the selected scope. -/
theorem SourceResolves.unique {u : Source.Syn .unit} {out d' : Source.Decl}
    (h : SourceResolves u scope out) (hd : d' ∈ u.env.declared (some scope) out.name) :
    d' = out := by
  rw [h] at hd
  exact List.mem_singleton.mp hd

/-- Under the obligation, at most one table position declares the name in
`scope`. Two assembled entries retaining one source name (overloads) therefore
refute it, although assembly succeeds. -/
theorem SourceResolves.position_unique {u : Source.Syn .unit} {out o o' : Source.Decl}
    {p q : Nat} (h : SourceResolves u scope out) (hne : out.name ≠ "")
    (hp : u.decls[p]? = some o) (hn : o.name = out.name) (hs : o.scope = some scope)
    (hq : u.decls[q]? = some o') (hn' : o'.name = out.name) (hs' : o'.scope = some scope) :
    p = q :=
  filter_singleton_index h hp (by simp [hn, hs, hne]) hq (by simp [hn', hs', hne])

end Solidity.Correctness.Lowering.Total.CalleeAliases
