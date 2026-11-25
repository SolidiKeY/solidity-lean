import Solidity.Correctness.Lowering.Total.ArgumentInference.Raw
import Solidity.Correctness.Lowering.Total.CalleeInference

/-!
# Discharging the argument obligations of call inference

`CalleeInference.alias_inferN` and `alias_infer` leave one obligation per
argument position `i`: `Typed.inferN` at the fuel the call passes it (`n - 1 - i`,
or `args.nodes.length + 2 - i` at `Typed.infer`'s fuel) returns the expected
type. For ordered argument lists drawn from the scalar families of
`ArgumentInference.Scalar` (`ScalarArgs`: decimal literals, locals at their slot
type, nested Boolean expressions) these follow from the syntax and the context
facts alone: each position has fewer nodes than its budget (`argExprs_nodes`),
so its family result applies (`scalarArgs_each`, `scalarArgs_each_infer`); the
list infers to the expected types in order (`scalarArgs_argsN`,
`scalarArgs_argsInfer`); and the call theorems specialise
(`alias_inferN_scalar`, `alias_infer_scalar`). On the decoder's own spelling
(`Tables.expr`/`exprs`, `ArgumentInference.Raw`), a raw call over raw scalar
arguments (`RawScalars`) is spelled and inferred with no argument premise left
(`alias_infer_raw`).

Arithmetic, reference and nested-call arguments are not covered; the selection
conditions of `alias_inferCall` stay premises. Decoder-lane obligations, not
admission conditions or premises of `lowerLoopsCorrect`.
-/
namespace Solidity.Correctness.Lowering.Total.ArgumentInference

open Semantics (lookupBy)
open Decode Decode.Callee CalleeAliases CalleeResolution CalleeSelection CalleeInference
open Source (STy Syn Typed TypedArgs)

variable {Γ : Source.Ctx}

/-- **Budget from the syntax**: position `i` of an argument list sits under `i`
earlier cons nodes, its own cons node and the end node. -/
theorem argExprs_nodes : ∀ {args : Syn (.list .expr)} {i : Nat} {a : Syn .expr},
    (argExprs args)[i]? = some a → a.nodes.length + i + 2 ≤ args.nodes.length
  | .nil, _, _, h => by simp [argExprs] at h
  | .cons e es, 0, a, h => by
      simp [argExprs] at h; subst h
      have : 1 ≤ es.nodes.length := by cases es <;> simp [Source.Syn.nodes]
      simp [Source.Syn.nodes]; omega
  | .cons e es, i + 1, a, h => by
      have := argExprs_nodes (args := es) (i := i) (by simpa [argExprs] using h)
      simp [Source.Syn.nodes]; omega

/-- **The obligations of `alias_inferN`** at fuel `n` above the list's node count:
position `i` at `n - 1 - i`. -/
theorem scalarArgs_each {args : Syn (.list .expr)} {σs : List STy} {n : Nat}
    (h : ScalarArgs Γ (argExprs args) σs) (hn : args.nodes.length < n) :
    ∀ i a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
      ∃ d, Typed.inferN (n - 1 - i) Γ a = some ⟨σ, d⟩ := fun i a σ hi hσ => by
  obtain ⟨d, hd⟩ := (h.get hi hσ).inferN
  have := argExprs_nodes hi
  exact ⟨d, hd _ (by omega)⟩

/-- **The obligations of `alias_infer`**: position `i` at
`args.nodes.length + 2 - i`, the fuel the call passes it under `Typed.infer`. -/
theorem scalarArgs_each_infer {args : Syn (.list .expr)} {σs : List STy}
    (h : ScalarArgs Γ (argExprs args) σs) :
    ∀ i a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
      ∃ d, Typed.inferN (args.nodes.length + 2 - i) Γ a = some ⟨σ, d⟩ := fun i a σ hi hσ => by
  obtain ⟨d, hd⟩ := (h.get hi hσ).inferN
  have := argExprs_nodes hi
  exact ⟨d, hd _ (by omega)⟩

/-- The list infers to the expected types, in order, at every fuel above its
node count. -/
theorem scalarArgs_argsN {args : Syn (.list .expr)} {σs : List STy} {n : Nat}
    (h : ScalarArgs Γ (argExprs args) σs) (hn : args.nodes.length < n) :
    ∃ da, TypedArgs.inferN n Γ args = some ⟨σs, da⟩ :=
  argsN_of_each (by have := argExprs_length_lt args; omega) h.length_eq (scalarArgs_each h hn)

/-- At `TypedArgs.infer`'s fuel. -/
theorem scalarArgs_argsInfer {args : Syn (.list .expr)} {σs : List STy}
    (h : ScalarArgs Γ (argExprs args) σs) : ∃ da, TypedArgs.infer Γ args = some ⟨σs, da⟩ :=
  scalarArgs_argsN h (Nat.lt_succ_self _)

variable {T : Tables} {R : CallSpellExt.Registry} {scope : String}
  {leadingParts : Source.Syn (.list (.part false))} {fs : List (Name × FunDecl)}
  {u : Source.Syn .unit} {args : Syn (.list .expr)} {σs ps : List STy}

/-- **`alias_inferN` over scalar arguments**: the per-argument premises follow
from `ScalarArgs` and fuel above the argument list's node count. -/
theorem alias_inferN_scalar {n : Nat} {a : Name} {fd : FunDecl} {source : SourceFunction}
    {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (hargs : ScalarArgs Γ (argExprs args) σs) (hn : args.nodes.length < n) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        TypedArgs.inferN n Γ args = some ⟨σs, da⟩ ∧
        Typed.inferN (n + 1) Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ :=
  alias_inferN h henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre
    (by have := argExprs_length_lt args; omega) hargs.length_eq (scalarArgs_each hargs hn)

/-- **`alias_infer` over scalar arguments**: at `Typed.infer`'s fuel, every
per-argument premise is derived from `ScalarArgs`. -/
theorem alias_infer_scalar {a : Name} {fd : FunDecl} {source : SourceFunction} {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (hargs : ScalarArgs Γ (argExprs args) σs) :
    ∃ out rs, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rs ∧
      ∃ (da : TypedArgs Γ args σs)
        (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
        (hsig : out.fnSig Γ.env = some (ps, rs)),
        Typed.infer Γ (.call (.ident source.name) (.positional args)) =
          some ⟨STy.ret rs, typedCall da hsel hsig⟩ :=
  alias_infer h henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre hargs.length_eq
    (scalarArgs_each_infer hargs)

/-- **On the decoder's spelling**: a raw call `f(rs)` of an alias-selected
callee over ordered raw scalar arguments is spelled by `Tables.expr` as
`f(args)`, `args` the spelled arguments, and infers at `Typed.infer`'s fuel to
the callee's ordered retained return slots; no argument premise is left. -/
theorem alias_infer_raw (Te : Tables) {rs : List RawExpr} {a : Name} {fd : FunDecl}
    {source : SourceFunction} {index : Nat}
    (h : withFunctions T R scope leadingParts fs = some u) (henv : Γ.env = u.env)
    (hsc : Γ.scope = some scope) (hl : lookupBy a fs = some fd)
    (hf : firstIndex a fs = some index) (hs : fd.sourceDecl = some source)
    (hne : source.name ≠ "") (hloc : (Γ.locals.map Prod.fst).idxOf? source.name = none)
    (hcall : callable fd = true) (hps : Slots fd.widths fd.params ps)
    (hfit : Source.argsFit Γ.isBase Γ.mapFree σs ps = true)
    (hothers : OthersReject Γ.isBase Γ.mapFree σs fs source.name index)
    (hpre : PrefixRejects Γ σs scope leadingParts source.name)
    (hraw : RawScalars Γ rs σs) :
    ∃ args, Te.exprs rs = some args ∧
      Te.expr (.call source.name rs) = some (.call (.ident source.name) (.positional args)) ∧
      ∃ out rets, fromMetadata T R scope fd = some out ∧ Slots fd.widths fd.rets rets ∧
        ∃ (da : TypedArgs Γ args σs)
          (hsel : (Γ.functions source.name).filter (fits Γ σs) = [out])
          (hsig : out.fnSig Γ.env = some (ps, rets)),
          Typed.infer Γ (.call (.ident source.name) (.positional args)) =
            some ⟨STy.ret rets, typedCall da hsel hsig⟩ := by
  obtain ⟨args, hargs, hA⟩ := hraw.exprs (T := Te)
  exact ⟨args, hargs, expr_call hargs,
    alias_infer_scalar h henv hsc hl hf hs hne hloc hcall hps hfit hothers hpre hA⟩

end Solidity.Correctness.Lowering.Total.ArgumentInference
