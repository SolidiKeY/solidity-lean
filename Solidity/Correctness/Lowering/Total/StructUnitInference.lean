import Solidity.Correctness.Lowering.Total.StructUnitInference.Leading

/-!
# Callee lookup, selection and call inference in an assembled mixed unit

Specializes `CalleeResolution`, `CalleeSelection` and `CalleeInference` to the unit of
a successful `StructUnit.build`: the contract, the generated structs, the optional
constructor and every state root (reference roots included), then the translated
functions, every declaration kept in order. Nothing is deduplicated.

The leading prefix is read from `StructDecode.decode` and
`ReferenceStatePlacement.prefixParts`: it has no function-kind declaration
(`leading_noFunction`), which discharges `PrefixRejects` for that actual prefix
(`build_prefixRejects`) without making struct, state or constructor names disjoint
from callable names. A colliding struct or root stays a candidate of the name
(`build_lookup`), but the callable functions of a nonempty name absent from locals
are exactly the callable entries retaining it, one per entry and in entry order
(`build_functions`); a local hides them all (`build_functions_local`), and a
noncallable entry is never among them (`build_entry_unreachable`). An alias selects
the first entry carrying it, whose declaration is in the actual lookup
(`build_alias_lookup`).

Selection and inference without the prefix premise: `build_entry_selected`,
`build_alias_inferCall`, `build_alias_inferN`, `build_alias_infer`. The dispatch order
(constant, arguments, conversion, struct, builtin, then `inferCall`) is kept: an entry
retaining the unshadowed name excludes the competing branches (`build_entry_notOther`,
`build_entry_dispatch`). Two accepting callable positions are ambiguous
(`build_entries_ambiguous`, `build_ambiguous_inferN`).

Residual obligations stay explicit hypotheses: the retained signature slots (`Slots`),
argument fit (`argsFit`), competing overloads (`OthersReject`) and each argument's
inference at its actual fuel. They are decoder-lane obligations, not premises of
`lowerLoopsCorrect`. Open: concrete execution agreement, metadata recovery, expression
completeness, whole-unit elaboration success and universal decoder coverage.
-/
namespace Solidity.Correctness.Lowering.Total.StructUnitInference

open Semantics (lookupBy)
open Source (Syn STy Typed TypedArgs)
open Decode Decode.Callee CalleeAliases CalleeResolution CalleeSelection CalleeInference
open StructUnit (build build_ok)
open ReferenceStatePlacement (prefixParts)

variable {T : Tables} {R : CallSpellExt.Registry} {C : Contract} {scope : String}
  {fs : List (Name × FunDecl)} {u : Syn .unit} {Γ : Source.Ctx} {σs : List STy}
  {x : String}

/-! ## The actual prefix -/

/-- **The assembled prefix**: a successful build hands `withFunctions` the structs and
the constructor/state prefix, none of whose declarations is a function, and that
prefix rejects every call. -/
theorem build_leading (h : build T R C scope fs = .ok u) :
    ∃ ss p, StructDecode.decode C = .ok ss ∧ prefixParts T R C = .ok p ∧
      withFunctions T R scope (appendParts ss p) fs = some u ∧
      (∀ d ∈ (appendParts ss p).collect (some scope), d.kind ≠ .function) ∧
      ∀ Γ σs x, PrefixRejects Γ σs scope (appendParts ss p) x := by
  obtain ⟨ss, p, hs, hp, hw⟩ := build_ok h
  exact ⟨ss, p, hs, hp, hw, leading_noFunction hs hp, leading_prefixRejects hs hp⟩

/-- `PrefixRejects` for the actual prefix of the build. -/
theorem build_prefixRejects (h : build T R C scope fs = .ok u) :
    ∃ ss p, withFunctions T R scope (appendParts ss p) fs = some u ∧
      PrefixRejects Γ σs scope (appendParts ss p) x := by
  obtain ⟨ss, p, _, _, hw, _, hr⟩ := build_leading h
  exact ⟨ss, p, hw, hr Γ σs x⟩

/-! ## Lookup and callable functions -/

/-- **Lookup in the unit**: the declarations of `x` in the contract scope are the
prefix declarations named `x` (structs, constructor, roots: kept even when they
collide with a function name), then every translated entry named `x`. -/
theorem build_lookup (h : build T R C scope fs = .ok u) :
    ∃ ss p, withFunctions T R scope (appendParts ss p) fs = some u ∧
      (∀ d ∈ prefixNamed scope (appendParts ss p) x, d.kind ≠ .function) ∧
      u.env.declared (some scope) x = candidates T R scope (appendParts ss p) fs x ∧
      u.env.lookup (some scope) x =
        if (candidates T R scope (appendParts ss p) fs x).isEmpty then
          u.env.declared none x
        else candidates T R scope (appendParts ss p) fs x := by
  obtain ⟨ss, p, _, _, hw, hk, _⟩ := build_leading h
  exact ⟨ss, p, hw, fun d hd => hk d (List.mem_filter.mp hd).1, declared_scope hw x,
    lookup_scope hw x⟩

/-- **Callable functions of a name in the unit**: for a nonempty name absent from
locals, exactly the callable entries retaining it, one per entry, in entry order. -/
theorem build_functions (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hx : x ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? x = none) :
    Γ.functions x = callableEntries T R scope fs x := by
  obtain ⟨ss, p, hs, hp, hw⟩ := build_ok h
  by_cases hc : candidates T R scope (appendParts ss p) fs x = []
  · have hnil : callableEntries T R scope fs x = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun o ho => ?_
      obtain ⟨e, he, hm, hn, _⟩ := callableEntries_entry ho
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
      have hmem := entry_candidate (leadingParts := appendParts ss p) hi hm (hn ▸ hx)
      rw [hn, hc] at hmem; cases hmem
    rw [hnil, functions_lookup hloc, henv, hsc, lookup_scope hw, hc]
    simp only [List.isEmpty_nil, if_true]
    exact List.filter_eq_nil_iff.mpr fun d hd => by simp [build_declared_none h d hd]
  · rw [functions_scope hw henv hsc hloc hc, leading_functions_nil hs hp, List.nil_append]

/-- Local shadowing: a local of the name leaves no callable function. -/
theorem build_functions_local {i : Nat} (hloc : (Γ.locals.map Prod.fst).idxOf? x = some i) :
    Γ.functions x = [] :=
  functions_local hloc

/-- A noncallable (e.g. external-only) entry is never a callable function of the unit. -/
theorem build_entry_unreachable {f : FunDecl} {out : Source.Decl}
    (hm : fromMetadata T R scope f = some out) (hcall : callable f = false)
    (hsc : Γ.scope = some scope) : out ∉ Γ.functions x :=
  entry_unreachable hm hcall hsc

/-- **First-alias lookup in the unit**: an alias selects the first entry carrying it;
its declaration, named by the retained source name, is in the actual lookup of that
name, and among the callable functions when the entry is callable and unshadowed. -/
theorem build_alias_lookup {a : Name} {fd : FunDecl} {source : SourceFunction}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env) (hsc : Γ.scope = some scope)
    (hl : lookupBy a fs = some fd) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") :
    ∃ index out, firstIndex a fs = some index ∧ fs[index]? = some (a, fd) ∧
      fromMetadata T R scope fd = some out ∧ out.name = source.name ∧
      out.scope = some scope ∧ out ∈ u.env.lookup (some scope) source.name ∧
      (callable fd = true → (Γ.locals.map Prod.fst).idxOf? source.name = none →
        out ∈ Γ.functions source.name) := by
  obtain ⟨ss, p, _, _, hw⟩ := build_ok h
  obtain ⟨index, out, source', hf, hi, _, hm, hs', hn, hsco, _⟩ := alias_entry hw hl
  cases hs.symm.trans hs'
  obtain ⟨o, so, hmo, hso, -, -, -, hk⟩ := alias_lookup hw hl
  cases hs.symm.trans hso
  cases hm.symm.trans hmo
  obtain ⟨-, -, hmem⟩ := hk hne
  refine ⟨index, out, hf, hi, hm, hn, hsco, hmem, fun hcall hloc => ?_⟩
  · rw [build_functions h henv hsc hne hloc]
    exact List.mem_filterMap.mpr ⟨(a, fd), List.mem_of_getElem? hi,
      by simp [hm, Option.filter, hn, hcall]⟩

/-! ## Selection and call inference in the unit -/

variable {ps rs : List STy} {args : Syn (.list .expr)} {n : Nat}

/-- **Selection in the unit**: `entry_selected` with the prefix condition discharged. -/
theorem build_entry_selected {index : Nat} {e : Name × FunDecl} {source : SourceFunction}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env) (hsc : Γ.scope = some scope)
    (hi : fs[index]? = some e) (hs : e.2.sourceDecl = some source) (hne : source.name ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable e.2 = true) (hps : Slots e.2.widths e.2.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index) :
    ∃ out rs, fromMetadata T R scope e.2 = some out ∧ Slots e.2.widths e.2.rets rs ∧
      (Γ.functions source.name).filter (fits Γ σs) = [out] ∧
      out.fnSig Γ.env = some (ps, rs) := by
  obtain ⟨_, _, hw, hpre⟩ := build_prefixRejects (Γ := Γ) (σs := σs) (x := source.name) h
  exact entry_selected hw henv hsc hi hs hne hloc hcall hps hfit hothers hpre

/-- **Ambiguity in the unit**: two callable accepting positions retaining the name
leave no singleton overload filter, even with equal declarations. -/
theorem build_entries_ambiguous {i j : Nat} {e e' : Name × FunDecl} {s s' : SourceFunction}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hx : x ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? x = none) (hij : i ≠ j)
    (hi : fs[i]? = some e) (hj : fs[j]? = some e') (hs : e.2.sourceDecl = some s)
    (hs' : e'.2.sourceDecl = some s') (hn : s.name = x) (hn' : s'.name = x)
    (hc : callable e.2 = true) (hc' : callable e'.2 = true)
    (ha : Accepts Γ.isBase Γ.mapFree σs e.2) (ha' : Accepts Γ.isBase Γ.mapFree σs e'.2)
    (o : Source.Decl) : (Γ.functions x).filter (fits Γ σs) ≠ [o] := by
  obtain ⟨ss, p, _, _, hw⟩ := build_ok h
  exact entries_ambiguous hw henv hsc hx hloc hij hi hj hs hs' hn hn' hc hc' ha ha' o

/-- **Branch selection from retained metadata**: an entry retaining the unshadowed
nonempty name excludes the conversion, struct and builtin branches, even when a
struct or root of the unit carries that name. -/
theorem build_entry_notOther {index : Nat} {e : Name × FunDecl} {source : SourceFunction}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env) (hsc : Γ.scope = some scope)
    (hi : fs[index]? = some e) (hs : e.2.sourceDecl = some source) (hne : source.name ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none) :
    NotOther Γ source.name := by
  obtain ⟨ss, p, _, _, hw⟩ := build_ok h
  exact entry_notOther hw henv hsc hi hs hne hloc

/-- **Dispatch order kept**: past the constant branch and successful argument
inference, such a call is `inferCall` on the inferred argument typing. -/
theorem build_entry_dispatch {index : Nat} {e : Name × FunDecl} {source : SourceFunction}
    {da : TypedArgs Γ args σs}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env) (hsc : Γ.scope = some scope)
    (hi : fs[index]? = some e) (hs : e.2.sourceDecl = some source) (hne : source.name ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hargs : TypedArgs.inferN n Γ args = some ⟨σs, da⟩) :
    Typed.inferN (n + 1) Γ (.call (.ident source.name) (.positional args)) =
      Source.inferCall Γ source.name args σs da :=
  inferN_call_dispatch hargs (build_entry_notOther h henv hsc hi hs hne hloc)

/-- Duplicate accepting entries in the unit: inference of the call fails. -/
theorem build_ambiguous_inferN {i j : Nat} {e e' : Name × FunDecl}
    {s s' : SourceFunction} {da : TypedArgs Γ args σs}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hx : x ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? x = none) (hij : i ≠ j)
    (hi : fs[i]? = some e) (hj : fs[j]? = some e') (hs : e.2.sourceDecl = some s)
    (hs' : e'.2.sourceDecl = some s') (hn : s.name = x) (hn' : s'.name = x)
    (hc : callable e.2 = true) (hc' : callable e'.2 = true)
    (ha : Accepts Γ.isBase Γ.mapFree σs e.2) (ha' : Accepts Γ.isBase Γ.mapFree σs e'.2)
    (hargs : TypedArgs.inferN n Γ args = some ⟨σs, da⟩) :
    Typed.inferN (n + 1) Γ (.call (.ident x) (.positional args)) = none := by
  obtain ⟨ss, p, _, _, hw⟩ := build_ok h
  exact ambiguous_inferN hw henv hsc hx hloc hij hi hj hs hs' hn hn' hc hc' ha ha' hargs

/-- **Typed selection for an alias in the unit**: `alias_inferCall` without the prefix
premise. -/
theorem build_alias_inferCall {a : Name} {fd : FunDecl} {source : SourceFunction}
    {index : Nat} (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (da : TypedArgs Γ args σs) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        Source.inferCall Γ source.name args σs da =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  obtain ⟨_, _, hw, hpre⟩ := build_prefixRejects (Γ := Γ) (σs := σs) (x := source.name) h
  exact alias_inferCall hw henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre da

/-- **Inferred return type of an alias in the unit**, from each argument's result at its
actual fuel: `alias_inferN` without the prefix premise. -/
theorem build_alias_inferN {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hn : (argExprs args).length < n) (hlen : σs.length = (argExprs args).length)
    (he : ∀ i a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
      ∃ d, Typed.inferN (n - 1 - i) Γ a = some ⟨σ, d⟩) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        TypedArgs.inferN n Γ args = some ⟨σs, da⟩ ∧
        Typed.inferN (n + 1) Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  obtain ⟨_, _, hw, hpre⟩ := build_prefixRejects (Γ := Γ) (σs := σs) (x := source.name) h
  exact alias_inferN hw henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre hn hlen he

/-- **At `Typed.infer`'s fuel in the unit**: `alias_infer` without the prefix premise. -/
theorem build_alias_infer {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hlen : σs.length = (argExprs args).length)
    (he : ∀ i a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
      ∃ d, Typed.inferN (args.nodes.length + 2 - i) Γ a = some ⟨σ, d⟩) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        Typed.infer Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  obtain ⟨_, _, hw, hpre⟩ := build_prefixRejects (Γ := Γ) (σs := σs) (x := source.name) h
  exact alias_infer hw henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre hlen he

end Solidity.Correctness.Lowering.Total.StructUnitInference
