import Solidity.Correctness.Lowering.Total.StructUnitInference.Leading

/-!
# Callee lookup, selection and call inference in an assembled mixed unit

Specializes `CalleeResolution`, `CalleeSelection` and `CalleeInference` to a successful
`StructUnit.build`: structs, optional constructor and every state root, then the
translated functions, every declaration kept in order, nothing deduplicated.

The leading prefix, read from `StructDecode.decode` and `prefixParts`, has no function
(`leading_noFunction`): that discharges `PrefixRejects` for it (`build_prefixRejects`)
without names disjoint from callable ones. A colliding struct or root stays a candidate
(`build_lookup`), yet the callable functions of a nonempty unshadowed name are exactly
its callable entries in entry order (`build_functions`; locals and noncallable entries:
the generic `functions_local`, `entry_unreachable`); first-alias lookup
(`build_alias_lookup`). Selection and inference without the prefix premise
(`build_entry_selected`, `build_alias_infer`); the dispatch order (constant, arguments,
conversion, struct, builtin, then `inferCall`) with the competing branches excluded by
a retained entry (`build_entry_notOther`, `build_entry_dispatch`); ambiguity
(`build_ambiguous_inferN`).

Residual hypotheses: signature slots, argument fit, `OthersReject` and each argument's
inference at its fuel: decoder-lane obligations, not premises of `lowerLoopsCorrect`.
Open: execution agreement, metadata recovery, expression completeness, whole-unit
elaboration success and universal decoder coverage.
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

/-- **First-alias lookup in the unit**: an alias selects the first entry carrying it;
its declaration carries the entry's retained source name and, for a nonempty name, is in
the actual lookup of that name, and among the callable functions when the entry is
callable and the name unshadowed. -/
theorem build_alias_lookup {a : Name} {fd : FunDecl}
    (h : build T R C scope fs = .ok u) (henv : Γ.env = u.env) (hsc : Γ.scope = some scope)
    (hl : lookupBy a fs = some fd) :
    ∃ index out source, firstIndex a fs = some index ∧ fs[index]? = some (a, fd) ∧
      fromMetadata T R scope fd = some out ∧ fd.sourceDecl = some source ∧
      out.name = source.name ∧ out.scope = some scope ∧
      (source.name ≠ "" → out ∈ u.env.lookup (some scope) source.name ∧
        (callable fd = true → (Γ.locals.map Prod.fst).idxOf? source.name = none →
          out ∈ Γ.functions source.name)) := by
  obtain ⟨ss, p, _, _, hw⟩ := build_ok h
  obtain ⟨index, out, source, hf, hi, _, hm, hs, hn, hsco, _⟩ := alias_entry hw hl
  obtain ⟨o, so, hmo, hso, -, -, -, hk⟩ := alias_lookup hw hl
  cases hs.symm.trans hso
  cases hm.symm.trans hmo
  refine ⟨index, out, source, hf, hi, hm, hs, hn, hsco, fun hne => ⟨(hk hne).2.2, ?_⟩⟩
  intro hcall hloc
  rw [build_functions h henv hsc hne hloc]
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
