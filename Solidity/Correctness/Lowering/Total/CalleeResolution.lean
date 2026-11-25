import Solidity.Correctness.Lowering.Total.CalleeAliases
import Solidity.Correctness.Lowering.Total.CalleeResolution.Lists

/-!
# Assembled callee declarations under Source name resolution

`CalleeAliases.alias_entry` takes a model alias lookup over a successful
`Callee.withFunctions` assembly to the declaration at the entry's position,
named by the entry's retained source name. This module reads that unit with the
existing Source resolution: `Env.declared`, `Env.linearize`, `Env.visible`,
`Env.lookup`, `Env.resolve` and `Source.Resolves`. No decoder or resolution
algorithm is added.

From the assembled syntax (`withFunctions_declarations`): the contract has no
bases, so its linearization is itself (`linearize_scope`); visibility in its
own scope keeps every declaration (`visible_self`); the declarations of a name
in the contract scope are exactly, in order, the matching scope declarations
of the supplied prefix followed by every matching translated function entry
(`declared_scope`, `candidates`), so overloads and entries sharing a retained
name all stay; lookup is that set when nonempty and the file level otherwise
(`lookup_scope`); nothing is found under the empty name (`lookup_empty`). For an alias-selected entry with a nonempty retained name the
declaration is in the actual lookup (`alias_lookup`); with the name absent from
locals, `Resolves` and `Env.resolve` give the whole declaration set
(`alias_resolves`), while a local of that name shadows it (`alias_local`, like `visible_self` a
generic fact of `Source.Resolves`, not of the assembly). The empty name has no
candidates (`candidates_empty`).

`DeclaredUniquely` follows from explicit retained-name uniqueness and prefix
noncollision (`alias_declaredUniquely`); both are obligations for the decoder
lane to discharge, not admission restrictions or premises of
`lowerLoopsCorrect`. Declaration-set resolution does not select an overloaded
callee and says nothing about argument typing, execution agreement,
inheritance reconstruction, complete coverage or simulation.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeResolution

open Semantics (lookupBy)
open Decode Decode.Callee CalleeAliases

variable {T : Tables} {R : CallSpellExt.Registry} {scope : String}
  {leadingParts : Source.Syn (.list (.part false))} {fs : List (Name × FunDecl)}
  {u : Source.Syn .unit}

/-- Prefix declarations named `x` directly in the contract scope, in order. -/
def prefixNamed (scope : String) (leadingParts : Source.Syn (.list (.part false)))
    (x : String) : List Source.Decl :=
  (leadingParts.collect (some scope)).filter fun d => d.scope == some scope && d.name == x

/-- Translated function entries whose declaration is named `x`, in entry
order, one per entry (duplicates and overloads kept). -/
def entriesNamed (T : Tables) (R : CallSpellExt.Registry) (scope : String)
    (fs : List (Name × FunDecl)) (x : String) : List Source.Decl :=
  fs.filterMap fun e => (fromMetadata T R scope e.2).filter fun d => d.name == x

/-- The ordered Source candidates for `x` in the assembled contract scope. -/
def candidates (T : Tables) (R : CallSpellExt.Registry) (scope : String)
    (leadingParts : Source.Syn (.list (.part false))) (fs : List (Name × FunDecl))
    (x : String) : List Source.Decl :=
  if x = "" then [] else prefixNamed scope leadingParts x ++ entriesNamed T R scope fs x

/-- Retained-name uniqueness: at most one entry position retains source name `x`. -/
def RetainedUniquely (fs : List (Name × FunDecl)) (x : String) : Prop :=
  ∀ (i j : Nat) (e e' : Name × FunDecl) (s s' : SourceFunction), fs[i]? = some e → fs[j]? = some e' → e.2.sourceDecl = some s →
    e'.2.sourceDecl = some s' → s.name = x → s'.name = x → i = j

/-- Prefix noncollision: no prefix declaration in the contract scope is named `x`. -/
def PrefixClear (scope : String) (leadingParts : Source.Syn (.list (.part false)))
    (x : String) : Prop :=
  ∀ d ∈ leadingParts.collect (some scope), d.scope = some scope → d.name ≠ x

theorem candidates_empty : candidates T R scope leadingParts fs "" = [] := rfl

/-! ## Facts read from the assembled syntax -/

/-- The assembled contract has no bases: its linearization is itself. -/
theorem linearize_scope (h : withFunctions T R scope leadingParts fs = some u) :
    u.env.linearize scope = some [scope] := by
  obtain ⟨_, _, _, hd⟩ := withFunctions_declarations h
  simp [Source.Syn.env, Source.Env.linearize, Source.Env.linearizeF, Source.Env.bases,
    Source.Env.bases.names, Source.inheritPaths, Source.Env.merge, hd]

/-- Visibility from a scope into itself keeps every declaration. -/
theorem visible_self (E : Source.Env) (s : Option String) (x : String) :
    E.visible s s x = E.declared s x := by
  simp [Source.Env.visible]

/-- The declarations of `x` directly in the contract scope are exactly the
ordered candidates: matching prefix declarations, then every matching
translated entry. -/
theorem declared_scope (h : withFunctions T R scope leadingParts fs = some u) (x : String) :
    u.env.declared (some scope) x = candidates T R scope leadingParts fs x := by
  obtain ⟨functions, hf, _, hd⟩ := withFunctions_declarations h
  have hF := functionParts_faithful T R scope fs functions hf
  have hsc : ∀ d ∈ functions.collect (some scope), d.scope = some scope := by
    intro d hm
    have : some d ∈ fs.map (fun f => fromMetadata T R scope f.2) := by
      rw [← hF]; exact List.mem_map_of_mem hm
    obtain ⟨e, _, he⟩ := List.mem_map.mp this
    obtain ⟨_, _, _, _, _, _, hs⟩ := fromMetadata_header he
    exact hs
  simp only [Source.Syn.env, Source.Env.declared, hd, List.filter_cons, List.filter_append]
  have h0 : ((none : Option String) == some scope) = false := rfl
  simp only [h0, Bool.false_and, Bool.false_eq_true, if_false]
  unfold candidates prefixNamed entriesNamed
  by_cases hx : x = ""
  · subst hx; simp
  · simp only [hx, if_false]
    rw [← filter_of_map_some _ _ _ _ hF]
    congr 1
    · exact List.filter_congr fun d _ => by simp [hx]
    · exact List.filter_congr fun d hm => by simp [hsc d hm, hx]

/-- Lookup in the contract scope: its own candidates when there are any, the
file level otherwise. -/
theorem lookup_scope (h : withFunctions T R scope leadingParts fs = some u) (x : String) :
    u.env.lookup (some scope) x =
      if (candidates T R scope leadingParts fs x).isEmpty then u.env.declared none x
      else candidates T R scope leadingParts fs x := by
  simp only [Source.Env.lookup, linearize_scope h, Option.getD_some, List.map_cons,
    List.map_nil]
  have hv : u.env.visible (some scope) (some scope) x = candidates T R scope leadingParts fs x :=
    (visible_self _ _ _).trans (declared_scope h x)
  simp only [List.find?_cons, List.find?_nil, hv]
  cases hc : candidates T R scope leadingParts fs x <;> simp [hv, hc]

/-- Empty-name boundary: nothing is found under `""` in the contract scope. -/
theorem lookup_empty (h : withFunctions T R scope leadingParts fs = some u) :
    u.env.lookup (some scope) "" = [] := by
  rw [lookup_scope h]
  simp [candidates, Source.Env.declared]

/-! ## The alias-selected declaration -/

/-- The declaration an alias lookup selects is among the translated entries
named by its retained name; for a nonempty name it is also a candidate, and
the actual lookup is the whole candidate set and contains it. -/
theorem alias_lookup {a : Name} {d : FunDecl}
    (h : withFunctions T R scope leadingParts fs = some u) (hl : lookupBy a fs = some d) :
    ∃ out source, fromMetadata T R scope d = some out ∧ d.sourceDecl = some source ∧
      out.name = source.name ∧ out.scope = some scope ∧
      out ∈ entriesNamed T R scope fs source.name ∧
      (source.name ≠ "" →
        out ∈ candidates T R scope leadingParts fs source.name ∧
        u.env.lookup (some scope) source.name = candidates T R scope leadingParts fs source.name ∧
        out ∈ u.env.lookup (some scope) source.name) := by
  obtain ⟨index, out, source, _, hi, _, hm, hs, hn, hsc, _⟩ := alias_entry h hl
  have he : out ∈ entriesNamed T R scope fs source.name :=
    List.mem_filterMap.mpr ⟨(a, d), List.mem_of_getElem? hi, by simp [hm, Option.filter, hn]⟩
  refine ⟨out, source, hm, hs, hn, hsc, he, fun hne => ?_⟩
  have hc : out ∈ candidates T R scope leadingParts fs source.name := by
    simp only [candidates, hne, if_false]; exact List.mem_append_right _ he
  have hk : u.env.lookup (some scope) source.name = candidates T R scope leadingParts fs source.name := by
    rw [lookup_scope h]
    cases hcs : candidates T R scope leadingParts fs source.name with
    | nil => rw [hcs] at hc; cases hc
    | cons _ _ => rfl
  exact ⟨hc, hk, hk ▸ hc⟩

/-- With the retained name absent from locals, Source resolution denotes the
whole candidate set (an overload set, not a selected callee). -/
theorem alias_resolves {a : Name} {d : FunDecl} {source : SourceFunction}
    {locals : List String}
    (h : withFunctions T R scope leadingParts fs = some u) (hl : lookupBy a fs = some d)
    (hs : d.sourceDecl = some source) (hne : source.name ≠ "")
    (hloc : locals.idxOf? source.name = none) :
    Source.Resolves u.env locals (some scope) source.name
        (.decls (candidates T R scope leadingParts fs source.name)) ∧
      u.env.resolve locals (some scope) source.name =
        some (.decls (candidates T R scope leadingParts fs source.name)) := by
  obtain ⟨out, source', _, hs', _, _, _, hk⟩ := alias_lookup h hl
  cases hs.symm.trans hs'
  obtain ⟨_, hk, hmem⟩ := hk hne
  have hr : Source.Resolves u.env locals (some scope) source.name
      (.decls (u.env.lookup (some scope) source.name)) :=
    .decl hloc (List.ne_nil_of_mem hmem)
  rw [hk] at hr
  exact ⟨hr, hr.resolve⟩

/-- Local shadowing: a local of the retained name hides every declaration. -/
theorem alias_local {x : String} {locals : List String} {i : Nat}
    (hloc : locals.idxOf? x = some i) :
    u.env.resolve locals (some scope) x = some (.loc i) :=
  (Source.Resolves.inLocals i hloc).resolve

/-! ## Deriving the scope-local uniqueness obligation -/

/-- `DeclaredUniquely` from retained-name uniqueness and prefix noncollision
(neither assumes the singleton lookup). -/
theorem alias_declaredUniquely {a : Name} {d : FunDecl} {source : SourceFunction}
    (h : withFunctions T R scope leadingParts fs = some u) (hl : lookupBy a fs = some d)
    (hs : d.sourceDecl = some source) (hne : source.name ≠ "")
    (huniq : RetainedUniquely fs source.name) (hpre : PrefixClear scope leadingParts source.name) :
    ∃ out, fromMetadata T R scope d = some out ∧ DeclaredUniquely u scope out := by
  obtain ⟨index, out, source', _, hi, _, hm, hs', hn, _, _⟩ := alias_entry h hl
  cases hs.symm.trans hs'
  refine ⟨out, hm, ?_⟩
  unfold DeclaredUniquely
  rw [hn, declared_scope h, candidates, if_neg hne, prefixNamed]
  rw [List.filter_eq_nil_iff.mpr fun p hp => by
    simpa using fun hps => hpre p hp hps, List.nil_append]
  refine filterMap_singleton _ fs hi (by simp [hm, Option.filter, hn]) fun j b o' hj hb => ?_
  simp only [Option.filter] at hb
  cases hb' : fromMetadata T R scope b.2 with
  | none => simp [hb'] at hb
  | some o =>
      simp only [hb'] at hb
      split at hb
      · rename_i hon
        obtain ⟨s, _, hsb, _, _, hns, _⟩ := fromMetadata_header hb'
        exact huniq j index b (a, d) s source hj hi hsb hs (by simpa [hns] using hon) rfl
      · cases hb

end Solidity.Correctness.Lowering.Total.CalleeResolution
