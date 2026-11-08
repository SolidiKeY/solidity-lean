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
(`NUpdElem.ownTy?`), so `find(old, count)` reads a local of type `old`; the
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
def specParams (C : Contract) (f : String) : Except String NCtx := do
  let some d := if f == "constructor" then C.ctor else Semantics.lookupBy f C.funs
    | throw s!"{f} is not a function of the contract"
  pure (ECtx.toNCtx (← d.paramCtx))

/-- The named output context and typed post from the actual shared modal
compiler. These fields are not reconstructed using default names. -/
structure SpecModalContextV1 (C : Contract) (input : NCtx) (call : SProg C)
    (posts : List (NRead C)) where
  output : Ctx
  program : Prog C input.ctx output
  chainEquation : SProg.chain input.names input.ctx call = .ok ⟨output, program⟩
  names : NCtx
  namesEquation : names = (program.outNames input.names).zip output
  contextEquation : names.ctx = output
  post : Fml C names.ctx
  postEquation : NRead.conj posts names = .ok post
  formula : Fml C input.ctx
  formulaEquation : formula = .modal .box program .nil (contextEquation ▸ post)

def specModalWithContextV1 (Δ : NCtx) (P : SProg C) (posts : List (NRead C)) :
    Except String (SpecModalContextV1 C Δ P posts) := do
  match chain : SProg.chain Δ.names Δ.ctx P with
  | .error reason => throw reason
  | .ok ⟨Γ', P'⟩ =>
    let Γn : NCtx := (P'.outNames Δ.names).zip Γ'
    if h : Γn.ctx = Γ' then
      let compiled ← rememberSpecResultV1 (NRead.conj posts Γn)
      pure {
        output := Γ', program := P', chainEquation := chain, names := Γn,
        namesEquation := rfl, contextEquation := h, post := compiled.val,
        postEquation := compiled.property, formula := .modal .box P' .nil (h ▸ compiled.val),
        formulaEquation := rfl }
    else throw "internal: the call leaves a context its names do not cover"

/-- `[ P ] (φ₁ ∧ … ∧ φₙ)` read in `Δ`: the call `P` placed there
(`SProg.chain`), the postconditions in the context it leaves. -/
def specModal (Δ : NCtx) (P : SProg C) (posts : List (NRead C)) : Except String (Fml C Δ.ctx) :=
  (specModalWithContextV1 Δ P posts).map (·.formula)

theorem specModalWithContextV1_forget (Δ : NCtx) (P : SProg C) (posts : List (NRead C)) :
    (specModalWithContextV1 Δ P posts).map (·.formula) = specModal Δ P posts := rfl

/-- The exact legacy obligation alongside contexts from its single shared
pieces/modal computations. Existing signatures and formulas remain projections. -/
structure SpecObligationContextV1 (C : Contract) (name : String) where
  formula : Fml C []
  pieces : SpecPiecesContextV1 C name
  modalInput : NCtx
  modal : SpecModalContextV1 C modalInput pieces.legacy.2.2.2.1 pieces.legacy.2.2.2.2

def specObligationWithContextV1 (C : Contract) (f : String) :
    Except String (SpecObligationContextV1 C f) := do
  let pieces ← specPiecesWithContextV1 C f
  let a := pieces.legacy.1
  let b := pieces.legacy.2.1
  let U := pieces.legacy.2.2.1
  let P := pieces.legacy.2.2.2.1
  let posts := pieces.legacy.2.2.2.2
  let Γ ← specParams C f
  let pre ← NRead.conj (a ++ b) Γ
  let (body, modal) ← if U.isEmpty then do
    let modal ← specModalWithContextV1 Γ P posts
    pure (modal.formula, (⟨Γ, modal⟩ : (input : NCtx) × SpecModalContextV1 C input P posts))
  else do
    let ⟨Δ, U'⟩ ← Upd.resolveN (fun _ => none) Γ Γ .nil U
    let modal ← specModalWithContextV1 Δ P posts
    pure (.upd .box U' modal.formula, (⟨Δ, modal⟩ : (input : NCtx) × SpecModalContextV1 C input P posts))
  pure {
    formula := Fml.closeN false Γ (.imp pre body), pieces,
    modalInput := modal.1, modal := modal.2 }

/-- **The obligation of `f`, scoped**: `R ∧ L ∧ M ∧ I ∧ requires → {old :=
storage ‖ oldNet := net ‖ B} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures ∧
A)` (`specPieces`), read in its parameters' context and closed by hidden
binders: the update declares `old` and `oldNet` at `LTy.old` and
`LTy.oldNet` (`Upd.resolveN`), the call is placed past them
(`specModal`), and the update is left out when it is empty. -/
def specObligation (C : Contract) (f : String) : Except String (Fml C []) :=
  (specObligationWithContextV1 C f).map (·.formula)

theorem specObligationWithContextV1_forget (C : Contract) (f : String) :
    (specObligationWithContextV1 C f).map (·.formula) = specObligation C f := rfl

/-- **The contract's invariant** (`invariant e;`, `Contract.inv`), a closed
formula of the storage: solkey's `CInv(storage, net)`, as `specObligation`
assumes and owes it, and as a callee keeps it under callbacks
(`docs/options.md`, O4). -/
def specInv (C : Contract) : Except String (Fml C []) := do
  let ctx : SpecCtx C := { storage := .storage, ensures := false, locals := [], result := none }
  let invs ← C.inv.mapM (SpecExpr.fml C ctx)
  NRead.conj invs ([] : NCtx)

end Resolve

/-- `cinv[C]`: `C`'s invariant (`specInv`), `Fml C []`. -/
syntax "cinv[" term "]" : term

/-- `invariant[C]`: `C`'s invariant as the `Invariant C` a callee keeps
(`ValidC invariant[C] spec[C]{f}`). -/
syntax "invariant[" term "]" : term

/-- `invariant!`: `invariant[C]` for the file's `InContract` contract. -/
syntax "invariant!" : term

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
      `((specObligation ($c) $(quote (f.getId.toString false))).map (Fml.quote $q))
  | `(cproblem[ $c:term ]{ constructor }) =>
    elabAgainst c fun q => `((Problem.ctor ($c) Modality.diamond).map (Fml.quote $q))
  | `(cinv[ $c:term ]) => elabAgainst c fun q => `((specInv ($c)).map (Fml.quote $q))

macro_rules
  | `(spec[ $c:term ]{ $f:ident }) => `(cspec[$c]{ $f })
  | `(invariant[ $c:term ]) =>
    `(({ fml := cinv[$c] } : $(Lean.mkIdent `Solidity.Invariant) $c))
  | `(invariant!) => `(invariant[InContract.contract])
  | `(cspec!{ $f:ident }) => `(cspec[InContract.contract]{ $f })
  | `(cproblem!{ constructor }) => `(cproblem[InContract.contract]{ constructor })

end Solidity
