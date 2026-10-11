import Solidity.Calculus.Problem
import Solidity.Calculus.NotationResolve
import Solidity.Calculus.Quote

/-!
# Specifications, scoped

`Calculus/SurfaceSpec.lean`'s specifications as scoped formulas, `Fml C
[]` (`docs/intrinsic.md`, M6b, W8): a specification's obligation
(`spec!{f}`, `specObligation`) is built from its pieces (`specPieces`) in
the parameters' context.  Its premises and postconditions, formulas over
names (`NRead`, `Calculus/NotationResolve.lean`), are read with their
locals as positions where they stand; its
snapshots are declared by its update at their own types (`Upd.resolveN`),
`old := storage` an `LTy.old` and `oldNet := net` an `LTy.oldNet`
(`UpdElem.ownTy?`), so `find(old, count)` reads a local of type `old`; the
call, elaborated scoped in the parameters' context, is placed past them
(`SProg.chain`), and `result` is declared by it.  The parameters are bound
by hidden binders (`Fml.bind`, every value), as the closer's free locals
range over every value: the premise `R` still gives each its range.

The plain obligations (`Problem.fml`, `Problem.ctorFml`, `Problem.ctor`)
are `Calculus/Problem.lean`'s; this module adds the scoped notation of
both, `cspec[C]{f}` (which `spec[C]{f}` and `spec!{f}` are) and
`cproblem[C]{constructor}`.
-/

namespace Solidity

open Solidity (Modality Op0 Op1 EnvKey)

variable {C : Contract}

/-! ## Specifications -/

section Resolve

variable [FreshNames]

/-- The parameters of the function `f` (`constructor` the constructor). -/
def specParams (C : Contract) (f : String) : Except String (List (PrimTy × Var)) := do
  let some d := if f == "constructor" then C.ctor else Semantics.lookupBy f C.funs
    | throw s!"{f} is not a function of the contract"
  d.params.mapM fun (n, T) => match T with
    | .prim p => pure (p, Var.ofName n)
    | _ => throw s!"{f}: the parameter {n} has a reference type"

/-- `[ P ] (φ₁ ∧ … ∧ φₙ)` read in `Δ`: the call `P` placed there
(`SProg.chain`), the postconditions in the context it leaves. -/
def specModal (Δ : NCtx) (P : SProg C) (posts : List (NRead C)) : Except String (Fml C Δ.ctx) := do
  let ⟨Γ', P'⟩ ← SProg.chain Δ.names Δ.ctx P
  let Γn : NCtx := (P'.outNames Δ.names).zip Γ'
  if h : Γn.ctx = Γ' then
    let post ← NRead.conj posts Γn
    pure (.modal .box P' .nil (h ▸ post))
  else throw "internal: the call leaves a context its names do not cover"

/-- **The obligation of `f`, scoped**: `R ∧ L ∧ M ∧ I ∧ requires → {old :=
storage ‖ oldNet := net ‖ B} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures ∧
A)` (`specPieces`), read in its parameters' context and closed by hidden
binders: the update declares `old` and `oldNet` at `LTy.old` and
`LTy.oldNet` (`Upd.resolveN`), the call is placed past them
(`specModal`), and the update is left out when it is empty. -/
def specObligation (C : Contract) (f : String) : Except String (Fml C []) := do
  let (a, b, U, P, posts) ← specPieces C f
  let Γ := paramsN (← specParams C f)
  let pre ← NRead.conj (a ++ b) Γ
  let body ← if U.isEmpty then specModal Γ P posts else do
    let ⟨Δ, U'⟩ ← Upd.resolveN (fun _ => none) Γ Γ .nil U
    pure (.upd .box U' (← specModal Δ P posts))
  pure (Fml.closeN false Γ (.imp pre body))

end Resolve

/-- `cspec[C]{f}`: `spec[C]{f}` scoped, `Fml C []`. -/
syntax "cspec[" term "]{ " ident " }" : term

/-- `cspec!{f}`: `cspec[C]{f}` for the file's `InContract` contract. -/
syntax "cspec!{ " ident " }" : term

/-- `cproblem[C]{constructor}`: `problem[C]{constructor}` (`Problem.ctor`), its scoped name. -/
syntax "cproblem[" term "]{ " &"constructor" " }" : term

/-- `cproblem!{constructor}`: `cproblem[C]{constructor}` for the file's
`InContract` contract. -/
syntax "cproblem!{ " &"constructor" " }" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(cspec[ $c:term ]{ $f:ident }) =>
    elabAgainst c fun q =>
      `((specObligation ($c) $(quote f.getId.toString)).map (Fml.quote $q))
  | `(cproblem[ $c:term ]{ constructor }) =>
    elabAgainst c fun q => `((Problem.ctor ($c) Modality.diamond).map (Fml.quote $q))

macro_rules
  | `(spec[ $c:term ]{ $f:ident }) => `(cspec[$c]{ $f })
  | `(cspec!{ $f:ident }) => `(cspec[InContract.contract]{ $f })
  | `(cproblem!{ constructor }) => `(cproblem[InContract.contract]{ constructor })

end Solidity
