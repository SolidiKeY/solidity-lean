import Solidity.Correctness.Lowering.Total.CalleeSelection.Entries
import Solidity.Source.Infer

/-!
# Typed callee selection from retained overload metadata

Reads `CalleeResolution.candidates` of an assembled `Callee.withFunctions`
unit with the existing Source call typing (`Ctx.functions`, `Decl.fnSig`,
`argsFit`, `Typed.callInternal`, `inferCall`); no decoder, resolution or
selection algorithm is added.

In the generated contract's scope the callable functions of a declared name
absent from locals are the callable prefix functions, then one declaration per
entry retaining the name with a callable role (`functions_scope`; signatures
by `callableEntries_entry` and `fromMetadata_signature`). Noncallable entries
are never among them (`entry_unreachable`); a local hides all (`functions_local`).

`entry_selected` derives the actual singleton overload filter from table-level
conditions: a nonempty unshadowed retained name, a callable role, accepting
retained parameter slots, and every other entry position retaining the name
(`OthersReject`) and matching prefix declaration (`PrefixRejects`) noncallable
or argument-incompatible. Two accepting callable positions are ambiguous even
with equal declarations (`entries_ambiguous`). `typedCall` is the
`Typed.callInternal` derivation; `inferCall_selected`, `alias_inferCall` show
`inferCall` returns it from supplied `TypedArgs`, `inferCall_none` the failure.

The conditions are decoder-lane obligations, not admission restrictions or
premises of `lowerLoopsCorrect`. No expression inference completeness,
execution agreement, inheritance reconstruction, coverage or simulation.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeSelection

open Semantics (lookupBy)
open Decode Decode.Callee CalleeAliases CalleeResolution
open Source (STy)

variable {T : Tables} {R : CallSpellExt.Registry} {scope : String}
  {leadingParts : Source.Syn (.list (.part false))} {fs : List (Name × FunDecl)}
  {u : Source.Syn .unit} {Γ : Source.Ctx} {σs : List STy} {x : String}

/-- Translations of the callable entries retaining source name `x`, one per entry, in order. -/
def callableEntries (T : Tables) (R : CallSpellExt.Registry) (scope : String)
    (fs : List (Name × FunDecl)) (x : String) : List Source.Decl :=
  fs.filterMap fun e => (fromMetadata T R scope e.2).filter fun d => d.name == x && callable e.2

/-- Every other entry position retaining `x` is noncallable or rejects the arguments. -/
def OthersReject (isBase : Source.DeclName → Source.DeclName → Bool)
    (mapFree : Source.DeclName → Bool) (σs : List STy) (fs : List (Name × FunDecl))
    (x : String) (index : Nat) : Prop :=
  ∀ (j : Nat) (e : Name × FunDecl) (s : SourceFunction), fs[j]? = some e → j ≠ index →
    e.2.sourceDecl = some s → s.name = x → callable e.2 = false ∨ ¬ Accepts isBase mapFree σs e.2

/-- Every prefix declaration named `x` is no callable function or rejects the arguments. -/
def PrefixRejects (Γ : Source.Ctx) (σs : List STy) (scope : String)
    (leadingParts : Source.Syn (.list (.part false))) (x : String) : Prop :=
  ∀ p ∈ prefixNamed scope leadingParts x,
    p.kind ≠ .function ∨ p.callableFrom (some scope) = false ∨ fits Γ σs p = false

/-! ## Callable functions of a name -/

/-- Without a local of the name: the visible functions of the actual lookup. -/
theorem functions_lookup (hloc : (Γ.locals.map Prod.fst).idxOf? x = none) :
    Γ.functions x =
      (Γ.env.lookup Γ.scope x).filter fun d => d.kind == .function && d.callableFrom Γ.scope := by
  simp only [Source.Ctx.functions, Source.Ctx.resolve, Source.Env.resolve, hloc]
  cases Γ.env.lookup Γ.scope x with
  | nil => cases Source.Builtin.ofName x <;> rfl
  | cons _ _ => rfl

/-- Local shadowing: a local of the name leaves no callable function. -/
theorem functions_local {i : Nat} (hloc : (Γ.locals.map Prod.fst).idxOf? x = some i) :
    Γ.functions x = [] := by
  simp only [Source.Ctx.functions, Source.Ctx.resolve, Source.Env.resolve, hloc]

/-- A translated entry is a candidate of its nonempty name. -/
theorem entry_candidate {index : Nat} {e : Name × FunDecl} {out : Source.Decl}
    (hi : fs[index]? = some e) (hm : fromMetadata T R scope e.2 = some out) (hx : out.name ≠ "") :
    out ∈ candidates T R scope leadingParts fs out.name := by
  simp only [candidates, hx, if_false]
  exact List.mem_append_right _ (List.mem_filterMap.mpr
    ⟨e, List.mem_of_getElem? hi, by simp [hm, Option.filter]⟩)

/-- A nonempty candidate list is the actual lookup. -/
theorem lookup_candidates (h : withFunctions T R scope leadingParts fs = some u)
    (hc : candidates T R scope leadingParts fs x ≠ []) :
    u.env.lookup (some scope) x = candidates T R scope leadingParts fs x := by
  rw [lookup_scope h]
  cases hcs : candidates T R scope leadingParts fs x with
  | nil => exact absurd hcs hc
  | cons _ _ => rfl

/-- Each callable entry declaration translates a callable entry retaining the name. -/
theorem callableEntries_entry {o : Source.Decl} (ho : o ∈ callableEntries T R scope fs x) :
    ∃ e ∈ fs, fromMetadata T R scope e.2 = some o ∧ o.name = x ∧ callable e.2 = true := by
  obtain ⟨e, he, hb⟩ := List.mem_filterMap.mp ho
  refine ⟨e, he, ?_⟩
  cases hm : fromMetadata T R scope e.2 with
  | none => simp [hm] at hb
  | some o' =>
      by_cases h1 : o'.name = x <;> by_cases h2 : callable e.2 = true <;>
        simp_all [Option.filter]

/-- Callable functions of a declared name: callable prefix functions, then callable entries. -/
theorem functions_scope (h : withFunctions T R scope leadingParts fs = some u)
    (henv : Γ.env = u.env) (hsc : Γ.scope = some scope)
    (hloc : (Γ.locals.map Prod.fst).idxOf? x = none)
    (hc : candidates T R scope leadingParts fs x ≠ []) :
    Γ.functions x =
      (prefixNamed scope leadingParts x).filter
          (fun d => d.kind == .function && d.callableFrom (some scope)) ++
        callableEntries T R scope fs x := by
  have hx : x ≠ "" := fun hx => hc (hx ▸ candidates_empty)
  rw [functions_lookup hloc, henv, hsc, lookup_candidates h hc]
  simp only [candidates, hx, if_false, List.filter_append, entriesNamed, callableEntries,
    List.filter_filterMap]
  congr 2
  funext e
  cases hm : fromMetadata T R scope e.2 with
  | none => rfl
  | some o =>
      by_cases hn : o.name = x <;>
        simp [Option.filter, hn, fromMetadata_callableFrom hm]

/-- A noncallable (e.g. external-only) entry is never a callable function, under any name. -/
theorem entry_unreachable {f : FunDecl} {out : Source.Decl}
    (hm : fromMetadata T R scope f = some out) (hcall : callable f = false)
    (hsc : Γ.scope = some scope) : out ∉ Γ.functions x := by
  intro hmem
  have hv := fromMetadata_callableFrom hm
  simp only [Source.Ctx.functions] at hmem
  split at hmem
  · rw [hsc, List.mem_filter, hv, hcall] at hmem
    exact Bool.false_ne_true hmem.2
  · cases hmem

/-! ## Selection -/

/-- **Selection**: the actual overload filter is the singleton of the entry's
translation, whose Source signature has the accepted parameter types. -/
theorem entry_selected {index : Nat} {e : Name × FunDecl} {source : SourceFunction}
    {ps : List STy} (h : withFunctions T R scope leadingParts fs = some u)
    (henv : Γ.env = u.env) (hsc : Γ.scope = some scope) (hi : fs[index]? = some e)
    (hs : e.2.sourceDecl = some source) (hne : source.name ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable e.2 = true) (hps : Slots e.2.widths e.2.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name) :
    ∃ out rs, fromMetadata T R scope e.2 = some out ∧ Slots e.2.widths e.2.rets rs ∧
      (Γ.functions source.name).filter (fits Γ σs) = [out] ∧
      out.fnSig Γ.env = some (ps, rs) := by
  obtain ⟨out, _, hm⟩ := withFunctions_entry h hi
  obtain ⟨source', _, ps', rs, hs', _, hn, _, _, _, hsig, hps', hrs⟩ :=
    fromMetadata_signature hm Γ.env
  cases hs.symm.trans hs'
  cases slots_unique hps hps'
  have hc : candidates T R scope leadingParts fs source.name ≠ [] :=
    List.ne_nil_of_mem (hn ▸ entry_candidate hi hm (hn ▸ hne))
  refine ⟨out, rs, hm, hrs, ?_, hsig⟩
  rw [functions_scope h henv hsc hloc hc, List.filter_append]
  rw [List.filter_eq_nil_iff.mpr fun p hp => by
    obtain ⟨hp, hq⟩ := List.mem_filter.mp hp
    rcases hpre p hp with hk | hk | hk <;> simp_all, List.nil_append]
  simp only [callableEntries, List.filter_filterMap]
  refine filterMap_singleton _ fs hi
    (by simp [hm, Option.filter, hn, hcall, (fromMetadata_fits hm Γ σs).mpr ⟨ps, hps, hfit⟩])
    fun j b o' hj hb => Classical.byContradiction fun hji => ?_
  cases hm' : fromMetadata T R scope b.2 with
  | none => simp [hm'] at hb
  | some o =>
      obtain ⟨s, _, _, _, hsb, _, hnb, _⟩ := fromMetadata_signature hm' Γ.env
      have hq : (o.name = source.name ∧ callable b.2 = true) ∧ fits Γ σs o = true := by
        by_cases h1 : o.name = source.name <;> by_cases h2 : callable b.2 = true <;>
          by_cases h3 : fits Γ σs o = true <;> simp_all [Option.filter]
      rcases hothers j b s hj hji hsb (hnb.symm.trans hq.1.1) with hk | hk
      · rw [hq.1.2] at hk; cases hk
      · exact hk ((fromMetadata_fits hm' Γ σs).mp hq.2)

/-- Positional ambiguity: two callable accepting positions retaining the name
leave no singleton overload filter, even when their declarations coincide. -/
theorem entries_ambiguous {i j : Nat} {e e' : Name × FunDecl} {s s' : SourceFunction}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hx : x ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? x = none) (hij : i ≠ j)
    (hi : fs[i]? = some e) (hj : fs[j]? = some e') (hs : e.2.sourceDecl = some s)
    (hs' : e'.2.sourceDecl = some s') (hn : s.name = x) (hn' : s'.name = x)
    (hc : callable e.2 = true) (hc' : callable e'.2 = true)
    (ha : Accepts Γ.isBase Γ.mapFree σs e.2) (ha' : Accepts Γ.isBase Γ.mapFree σs e'.2)
    (o : Source.Decl) : (Γ.functions x).filter (fits Γ σs) ≠ [o] := by
  intro ho
  obtain ⟨out, hp, hm⟩ := withFunctions_entry h hi
  obtain ⟨out', hp', hm'⟩ := withFunctions_entry h hj
  obtain ⟨t, _, _, _, ht, _, hnt, hst, _⟩ := fromMetadata_signature hm Γ.env
  obtain ⟨t', _, _, _, ht', _, hnt', hst', _⟩ := fromMetadata_signature hm' Γ.env
  cases hs.symm.trans ht
  cases hs'.symm.trans ht'
  have hxo : out.name = x := hnt.trans hn
  rw [functions_lookup hloc, henv, hsc, lookup_candidates h
    (List.ne_nil_of_mem (hxo ▸ entry_candidate hi hm (hxo ▸ hx)))] at ho
  rw [← declared_scope h, Source.Env.declared, List.filter_filter, List.filter_filter] at ho
  have hpos := filter_singleton_index ho hp
    (by simp [hst, hnt, hn, hx, fromMetadata_callableFrom hm, hc,
      (fromMetadata_fits hm Γ σs).mpr ha]) hp'
    (by simp [hst', hnt', hn', hx, fromMetadata_callableFrom hm', hc',
      (fromMetadata_fits hm' Γ σs).mpr ha'])
  exact hij (by simpa [entryPosition] using hpos)

/-! ## Typing the call -/

variable {f : String} {args : Source.Syn (.list .expr)} {d : Source.Decl} {ps rs : List STy}

/-- The `Typed.callInternal` derivation of a selected callee. -/
def typedCall (da : Source.TypedArgs Γ args σs)
    (hsel : (Γ.functions f).filter (fits Γ σs) = [d]) (hsig : d.fnSig Γ.env = some (ps, rs)) :
    Source.Typed Γ (.call (.ident f) (.positional args)) (STy.ret rs) :=
  .callInternal da hsel hsig

/-- Call inference succeeds with the selected callee's derivation. -/
theorem inferCall_selected (da : Source.TypedArgs Γ args σs)
    (hsel : (Γ.functions f).filter (fits Γ σs) = [d]) (hsig : d.fnSig Γ.env = some (ps, rs)) :
    Source.inferCall Γ f args σs da = some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  unfold Source.inferCall
  split
  · rename_i d' hf
    obtain rfl : d' = d := List.head_eq_of_cons_eq (hf.symm.trans hsel)
    split
    · rename_i ps' rs' hs'
      cases hs'.symm.trans hsig
      rfl
    · rename_i hs'
      cases hs'.symm.trans hsig
  · rename_i hno
    exact absurd hsel (hno d)

/-- Call inference fails when the overload filter is not a singleton. -/
theorem inferCall_none (da : Source.TypedArgs Γ args σs)
    (hno : ∀ o, (Γ.functions f).filter (fits Γ σs) ≠ [o]) :
    Source.inferCall Γ f args σs da = none := by
  unfold Source.inferCall
  split
  · rename_i d' hf
    exact absurd hf (hno d')
  · rfl

/-- **Typed selection for a model alias**: the alias-selected entry is the unique
overload, and inference returns its derivation from any supplied argument typing. -/
theorem alias_inferCall {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (da : Source.TypedArgs Γ args σs) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        Source.inferCall Γ source.name args σs da =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  obtain ⟨i, hfi, hi⟩ := Iff.mp lookupBy_eq_some_iff hl
  cases hf.symm.trans hfi
  obtain ⟨out, rs, hm, hrs, hsel, hsig⟩ :=
    entry_selected h henv hsc hi hs hne hloc hcall hps hfit hothers hpre
  exact ⟨out, rs, hm, hrs, hsel, hsig, inferCall_selected da hsel hsig⟩

end Solidity.Correctness.Lowering.Total.CalleeSelection
