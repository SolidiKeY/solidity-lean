import Solidity.Correctness.Lowering.Total.CalleeInference.Dispatch
import Solidity.Correctness.Lowering.Total.CalleeSelection

/-!
# Actual call inference for a selected callee

Connects the internal-call branch of `Source.Typed.inferN` to `CalleeSelection`.
A singleton overload filter excludes the competing branches, so inference
returns the `Typed.callInternal` derivation (`inferN_call_selected`). In an
assembled `Callee.withFunctions` scope an entry retaining the unshadowed name
excludes them (`entry_notOther`); with `alias_inferCall` and individual
argument results at their actual fuels an alias-selected entry infers to
`STy.ret rs` over its ordered retained return slots (`alias_inferN`), also at
`Typed.infer`'s fuel (`alias_infer`). Failing arguments, no or several matches,
duplicate entries and a local of the name leave `none`.

The hypotheses are decoder-lane obligations, not admission conditions or
premises of `lowerLoopsCorrect`; no expression inference completeness.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeInference

open Semantics (lookupBy)
open Decode Decode.Callee CalleeAliases CalleeResolution CalleeSelection
open Source (STy Syn Typed TypedArgs Decl)

variable {Γ : Source.Ctx} {n : Nat} {f : String} {args : Syn (.list .expr)} {σs : List STy}
  {d : Decl} {ps rs : List STy}

/-- **Selected call**: with the arguments inferred and a singleton overload
filter, inference returns the selected callee's derivation. -/
theorem inferN_call_selected {da : TypedArgs Γ args σs}
    (hargs : TypedArgs.inferN n Γ args = some ⟨σs, da⟩)
    (hsel : (Γ.functions f).filter (fits Γ σs) = [d]) (hsig : d.fnSig Γ.env = some (ps, rs)) :
    Typed.inferN (n + 1) Γ (.call (.ident f) (.positional args)) =
      some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  have hd : d ∈ Γ.functions f := (List.mem_filter.mp (hsel ▸ List.mem_singleton_self d)).1
  rw [inferN_call_dispatch hargs (notOther_of_functions hd)]
  exact inferCall_selected da hsel hsig

/-- A position failing at its actual fuel fails the call. -/
theorem inferN_call_fail_at {i : Nat} {a : Syn .expr} (hi : (argExprs args)[i]? = some a)
    (hf : Typed.inferN (n - 1 - i) Γ a = none) :
    Typed.inferN (n + 1) Γ (.call (.ident f) (.positional args)) = none :=
  inferN_call_args_none (argsN_fail_at hi hf)

/-- No or several matching overloads, competing branches excluded: no result. -/
theorem inferN_call_none {da : TypedArgs Γ args σs}
    (hargs : TypedArgs.inferN n Γ args = some ⟨σs, da⟩) (ho : NotOther Γ f)
    (hno : ∀ o, (Γ.functions f).filter (fits Γ σs) ≠ [o]) :
    Typed.inferN (n + 1) Γ (.call (.ident f) (.positional args)) = none := by
  rw [inferN_call_dispatch hargs ho]
  exact inferCall_none da hno

/-- Local shadowing: a local of the callee name leaves no internal call. -/
theorem local_inferN {da : TypedArgs Γ args σs} {i : Nat}
    (hargs : TypedArgs.inferN n Γ args = some ⟨σs, da⟩)
    (hloc : (Γ.locals.map Prod.fst).idxOf? f = some i) :
    Typed.inferN (n + 1) Γ (.call (.ident f) (.positional args)) = none :=
  inferN_call_none hargs (notOther_local hloc) fun o h => by
    rw [functions_local hloc] at h; cases h

variable {T : Tables} {R : CallSpellExt.Registry} {scope : String}
  {leadingParts : Source.Syn (.list (.part false))} {fs : List (Name × FunDecl)}
  {u : Source.Syn .unit}

/-- An entry retaining the unshadowed nonempty callee name excludes the competing
branches: the name denotes the candidates, among them that entry's function. -/
theorem entry_notOther {index : Nat} {e : Name × FunDecl} {source : SourceFunction}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hi : fs[index]? = some e)
    (hs : e.2.sourceDecl = some source) (hne : source.name ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none) :
    NotOther Γ source.name := by
  obtain ⟨out, _, hm⟩ := withFunctions_entry h hi
  obtain ⟨source', _, _, _, hs', _, hn, _, hk, _⟩ := fromMetadata_signature hm Γ.env
  cases hs.symm.trans hs'
  have hc := entry_candidate (leadingParts := leadingParts) hi hm (hn ▸ hne)
  rw [hn] at hc
  have hl := lookup_candidates h (List.ne_nil_of_mem hc)
  refine notOther_of_function (ds := u.env.lookup (some scope) source.name) ?_ (hl ▸ hc) hk
  simp only [Source.Ctx.resolve, Source.Env.resolve, hloc, henv, hsc, hl]
  cases hcs : candidates T R scope leadingParts fs source.name with
  | nil => rw [hcs] at hc; cases hc
  | cons _ _ => rfl

/-- Duplicate accepting entries (equal declarations included): inference fails. -/
theorem ambiguous_inferN {x : String} {i j : Nat} {e e' : Name × FunDecl}
    {s s' : SourceFunction} {da : TypedArgs Γ args σs}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hx : x ≠ "")
    (hloc : (Γ.locals.map Prod.fst).idxOf? x = none) (hij : i ≠ j)
    (hi : fs[i]? = some e) (hj : fs[j]? = some e') (hs : e.2.sourceDecl = some s)
    (hs' : e'.2.sourceDecl = some s') (hn : s.name = x) (hn' : s'.name = x)
    (hc : callable e.2 = true) (hc' : callable e'.2 = true)
    (ha : Accepts Γ.isBase Γ.mapFree σs e.2) (ha' : Accepts Γ.isBase Γ.mapFree σs e'.2)
    (hargs : TypedArgs.inferN n Γ args = some ⟨σs, da⟩) :
    Typed.inferN (n + 1) Γ (.call (.ident x) (.positional args)) = none := by
  subst hn
  exact inferN_call_none hargs (entry_notOther h henv hsc hi hs hx hloc)
    (entries_ambiguous h henv hsc hx hloc hij hi hj hs hs' rfl hn' hc hc' ha ha')

/-- **Inferred return type of an alias-selected callee**: from `alias_inferCall`'s
conditions and argument results at their actual fuels, the call infers to
`STy.ret rs`, `rs` the ordered retained return slots. -/
theorem alias_inferN {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
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
  obtain ⟨da, hargs⟩ := argsN_of_each hn hlen he
  obtain ⟨out, rs, hm, hrs, hsel, hsig, _⟩ :=
    alias_inferCall h henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre da
  exact ⟨out, rs, hm, hrs, da, hsel, hsig, hargs, inferN_call_selected hargs hsel hsig⟩

/-- An argument list has more nodes than positions. -/
theorem argExprs_length_lt : ∀ es : Syn (.list .expr), (argExprs es).length < es.nodes.length
  | .nil => by simp [argExprs, Source.Syn.nodes]
  | .cons _ es => by
      have := argExprs_length_lt es
      simp [argExprs, Source.Syn.nodes]; omega

/-- The node count of `f(args)`. -/
theorem call_nodes :
    (Syn.call (.ident f) (.positional args) : Syn .expr).nodes.length = args.nodes.length + 3 := by
  simp [Source.Syn.nodes]

/-- **At `Typed.infer`'s fuel**: the residual obligations are position `i` at the
fuel the call passes it, `args.nodes.length + 2 - i` (no fuel monotonicity). -/
theorem alias_infer {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (hlen : σs.length = (argExprs args).length)
    (he : ∀ i a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
      ∃ d, Typed.inferN (args.nodes.length + 2 - i) Γ a = some ⟨σ, d⟩) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        Typed.infer Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  have hlt := argExprs_length_lt args
  obtain ⟨out, rs, hm, hrs, da, hsel, hsig, _, hinf⟩ :=
    alias_inferN (n := args.nodes.length + 3) h henv hsc hl hf hs hne hloc hcall hps hfit
      hothers hpre (by omega) hlen fun i a σ hi hσ => by
        simpa [Nat.sub_sub, Nat.add_comm] using he i a σ hi hσ
  refine ⟨out, rs, hm, hrs, da, hsel, hsig, ?_⟩
  unfold Typed.infer; rw [call_nodes]; exact hinf

end Solidity.Correctness.Lowering.Total.CalleeInference
