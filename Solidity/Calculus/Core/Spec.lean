import Solidity.Calculus.Problem
import Solidity.Calculus.Core.NotationResolve
import Solidity.Calculus.Core.Quote

/-!
# Obligations and specifications, scoped

`Calculus/Problem.lean`'s obligations and `Calculus/Spec.lean`'s
specifications as scoped formulas, `Core.Fml C []` (`docs/intrinsic.md`,
M6b): the program is read in the context of the parameters, so every local
the obligation reads is bound in it.

* **A plain obligation** `∀x̄. wt(storage) → [ P ] true` (`Problem.fml`) and
  **a deployment's** `∀x̄. {deployUpd} [ P ] true` (`Problem.ctorFml`) take
  the program at the parameters' context `paramsN xs` (the first parameter
  outermost, so its position the deepest) and bind it by `∀` over each
  type's range, as today's `Fml.alls` does: `(Problem.fml m xs P).erase []`
  is today's, `P` erased.
* **A specification's obligation** (`spec!{f}`, `Core.specObligation`) is
  today's, read in the parameters' context (`Fml.resolveN`): its snapshots
  are declared by its update at their own types, `old := storage` an
  `LTy.old` and `oldNet := net` an `LTy.oldNet` (`UpdElem.ownTy?`), so
  `find(old, count)` reads a local of type `old`, and `result` is declared
  by the box's program.  The parameters are bound by hidden binders
  (`Fml.bind`, every value), as today's free locals range over every value:
  the premise `R` still gives each its range, and the erasure is today's
  obligation, exactly.
-/

namespace Solidity.Core

open Solidity (Modality Op0 Op1 EnvKey)

variable {C : Contract}

/-! ## Plain obligations -/

/-- The parameters `xs` as a named context, the first parameter the
outermost (deepest) local. -/
def paramsN (xs : List (PrimTy × Var)) : NCtx := xs.reverse.map fun (p, x) => (x, .val p)

/-- `wt(storage)`: the storage is one `C` can be in (`Problem.lean`'s
`Fml.wt`). -/
def Fml.wt (C : Contract) {Γ : Ctx} : Fml C Γ :=
  .defined (.app1 (.wt C.vars) rfl (.app0 .storage))

/-- solkey's obligation of a function of parameters `xs` and body `P`, read
in their context: `∀xs. wt(storage) → [ P ] true`, or the diamond. -/
def Problem.fml (m : Modality) (xs : List (PrimTy × Var)) {Γ' : Ctx}
    (P : Prog C (paramsN xs).ctx Γ') : Fml C [] :=
  Fml.closeN true (paramsN xs) (.imp (Fml.wt C) (.modal m P .nil .tt))

/-- solkey's deployment update, `{storage := mtSt ‖ net := storeSt(mtSt,
at(msgSender), msgValue) ‖ selfBalance := msgValue}` (`Problem.deployUpd`). -/
def Problem.deployUpd (C : Contract) {Γ : Ctx} : Upd C Γ Γ :=
  ((Upd.nil.snoc (.storage (.app0 (.mtSt C.vars)))).snoc
    (.netMt (.app0 (.env .msgSender)) (.app0 (.env .msgValue)))).snoc
    (.setBalance (.app0 (.env .msgValue)))

/-- solkey's obligation of a constructor of parameters `xs`, deployed by `P`
(`constructor(x̄);`): `∀xs. {deployUpd} [ P ] true`, or the diamond. -/
def Problem.ctorFml (m : Modality) (xs : List (PrimTy × Var)) {Γ' : Ctx}
    (P : Prog C (paramsN xs).ctx Γ') : Fml C [] :=
  Fml.closeN true (paramsN xs) (.upd m (Problem.deployUpd C) (.modal m P .nil .tt))

section Resolve

variable [FreshNames]

/-- An obligation's program resolved in its parameters' context, and the
obligation stated: a deployment's when `ctor`. -/
def Problem.resolve (ctor : Bool) (m : Modality) (xs : List (PrimTy × Var))
    (P : Solidity.Prog C) : Except String (Fml C []) := do
  let ⟨_, P'⟩ ← Prog.resolve (paramsN xs) P
  pure (if ctor then Problem.ctorFml m xs P' else Problem.fml m xs P')

/-- Today's obligation (`Solidity.Problem.fml`, `Solidity.Problem.ctorFml`)
scoped: its parts read back (`Problem.parts`), its program resolved. -/
def Problem.ofLegacy (φ : Solidity.Fml C) : Except String (Fml C []) :=
  match Solidity.Problem.parts φ with
  | some (xs, ctor, m, P) => Problem.resolve ctor m xs P
  | none => .error "not an obligation `∀x̄. wt(storage) → [ P ] true` or a deployment's"

/-- A constructor's obligation with no specification, scoped
(`Solidity.Problem.ctor`). -/
def Problem.ctor (C : Contract) (m : Modality) : Except String (Fml C []) := do
  Problem.ofLegacy (← Solidity.Problem.ctor C m)

/-! ## Specifications -/

/-- The parameters of the function `f` (`constructor` the constructor). -/
def specParams (C : Contract) (f : String) : Except String (List (PrimTy × Var)) := do
  let some d := if f == "constructor" then C.ctor else Semantics.lookupBy f C.funs
    | throw s!"{f} is not a function of the contract"
  d.params.mapM fun (n, T) => match T with
    | .prim p => pure (p, Var.ofName n)
    | _ => throw s!"{f}: the parameter {n} has a reference type"

/-- **The obligation of `f`, scoped**: `specObligation`'s, read in its
parameters' context and closed by hidden binders; `old` and `oldNet` are
declared by its update, at `LTy.old` and `LTy.oldNet`. -/
def specObligation (C : Contract) (f : String) : Except String (Fml C []) := do
  let φ ← Solidity.specObligation C f
  let Γ := paramsN (← specParams C f)
  pure (Fml.closeN false Γ (← Fml.resolveN (fun _ => none) Γ φ))

end Resolve

/-- `cspec[C]{f}`: `spec[C]{f}` scoped, `Core.Fml C []`. -/
syntax "cspec[" term "]{ " ident " }" : term

/-- `cspec!{f}`: `cspec[C]{f}` for the file's `InContract` contract. -/
syntax "cspec!{ " ident " }" : term

/-- `cproblem[C]{constructor}`: `problem[C]{constructor}` scoped. -/
syntax "cproblem[" term "]{ " &"constructor" " }" : term

/-- `cproblem!{constructor}`: `cproblem[C]{constructor}` for the file's
`InContract` contract. -/
syntax "cproblem!{ " &"constructor" " }" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(cspec[ $c:term ]{ $f:ident }) =>
    elabAgainst c fun q =>
      `((Core.specObligation ($c) $(quote f.getId.toString)).map (Core.Fml.quote $q))
  | `(cproblem[ $c:term ]{ constructor }) =>
    elabAgainst c fun q => `((Core.Problem.ctor ($c) Modality.diamond).map (Core.Fml.quote $q))

macro_rules
  | `(cspec!{ $f:ident }) => `(cspec[InContract.contract]{ $f })
  | `(cproblem!{ constructor }) => `(cproblem[InContract.contract]{ constructor })

end Solidity.Core
