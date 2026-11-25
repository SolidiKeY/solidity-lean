import Solidity.Correctness.Lowering.Total.ArithmeticInference.Budget
import Solidity.Correctness.Lowering.Total.CalleeInference

/-!
# Arithmetic argument inference for selected calls

Discharges the arithmetic argument family left open by `CalleeInference`:
`alias_inferN_arith` (`alias_inferN_arith_nodes`) and `alias_infer_arith` are `alias_inferN` and
`alias_infer` with their length and per-argument premises derived, for any
ordered list, from `Infers` (`ArithmeticInference/Fragment.lean`) at the
position-dependent budgets (`ArithmeticInference/Budget.lean`); a rejected
argument fails the call at every fuel (`call_rejected`).

The decoder and composition lane consumes these; reference and nested-call
arguments, mixed families, Boolean-only recursion, semantic binding and
universal coverage stay there. No statement here is an admission condition of
`lowerLoopsCorrect`.
-/

namespace Solidity.Correctness.Lowering.Total.ArithmeticInference

open Semantics (lookupBy)
open Decode Decode.Callee CalleeAliases CalleeResolution CalleeSelection CalleeInference
open Source (STy Syn Typed TypedArgs Decl)

variable {Γ : Source.Ctx} {T : Tables} {R : CallSpellExt.Registry} {scope : String}
  {leadingParts : Source.Syn (.list (.part false))} {fs : List (Name × FunDecl)}
  {u : Source.Syn .unit} {es : List RawExpr} {args : Syn (.list .expr)} {σs ps : List STy}
  {n : Nat}

/-- A model call is spelled over its spelled argument list. -/
theorem expr_call {f : String} (hs : T.exprs es = some args) :
    T.expr (.call f es) = some (.call (.ident f) (.positional args)) := by
  simp only [Tables.expr, hs, Option.map_some]

/-- **Alias-selected call over arithmetic arguments**, at `TypedArgs.inferN`'s
fuels: `alias_inferN` with its length and per-argument premises derived from
the family, given each position's budget. -/
theorem alias_inferN_arith {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (hargs : T.exprs es = some args) (hlen : σs.length = es.length)
    (hty : ∀ (i : Nat) e σ, es[i]? = some e → σs[i]? = some σ → Infers Γ e σ)
    (hn : es.length < n) (hfuel : ∀ (i : Nat) e, es[i]? = some e → depth e ≤ n - 1 - i) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        TypedArgs.inferN n Γ args = some ⟨σs, da⟩ ∧
        Typed.inferN (n + 1) Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  obtain ⟨hl', he⟩ := args_inferN hargs hlen hty hfuel
  exact alias_inferN h henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre
    (by rw [(exprs_get hargs).1]; exact hn) hl' he

/-- The same at any fuel from the argument list's node count: no budget premise. -/
theorem alias_inferN_arith_nodes {a : Name} {fd : FunDecl} {source : SourceFunction}
    {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (hargs : T.exprs es = some args) (hlen : σs.length = es.length)
    (hty : ∀ (i : Nat) e σ, es[i]? = some e → σs[i]? = some σ → Infers Γ e σ)
    (hn : args.nodes.length ≤ n) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        TypedArgs.inferN n Γ args = some ⟨σs, da⟩ ∧
        Typed.inferN (n + 1) Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ :=
  alias_inferN_arith h henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre hargs hlen hty
    (by have := argExprs_length_lt args; rw [(exprs_get hargs).1] at this; omega)
    fun i e he => by have := args_budget hargs he; omega

/-- **Alias-selected call over arithmetic arguments at `Typed.infer`'s fuel**:
`alias_infer` with its length and per-argument premises derived from the
family; no fuel hypothesis. -/
theorem alias_infer_arith {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (hargs : T.exprs es = some args) (hlen : σs.length = es.length)
    (hty : ∀ (i : Nat) e σ, es[i]? = some e → σs[i]? = some σ → Infers Γ e σ) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        Typed.infer Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ := by
  obtain ⟨hl', he⟩ := args_infer hargs hlen hty
  exact alias_infer h henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre hl' he

/-- **A rejected arithmetic argument fails the call** at every fuel. -/
theorem call_rejected {f : String} {i : Nat} {e : RawExpr} {r : Reason}
    (hargs : T.exprs es = some args) (hi : es[i]? = some e) (hr : Rejects Γ e r) :
    Typed.inferN n Γ (.call (.ident f) (.positional args)) = none := by
  cases n with
  | zero => exact inferN_zero
  | succ n =>
    obtain ⟨hl, hg⟩ := exprs_get hargs
    have hlt : i < (argExprs args).length := by
      rw [hl]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨e', he', ha⟩ := hg i _ (List.getElem?_eq_getElem hlt)
    cases hi.symm.trans he'
    exact inferN_call_fail_at (List.getElem?_eq_getElem hlt) ((hr.sound ha).2 _)

end Solidity.Correctness.Lowering.Total.ArithmeticInference
