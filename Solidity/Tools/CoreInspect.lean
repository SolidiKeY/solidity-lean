import Solidity.Tools.Inspect
import Solidity.Calculus.Core.Delab
import Solidity.Calculus.Core.Quote

/-!
# `#wp` and `#step` on scoped formulas

`Tools/Inspect.lean`'s `#wp φ` and `#step φ`, for a formula `φ : Core.Fml C Γ`
(`cdl!{ … }`, `Calculus/Core/Notation.lean`): the scoped strategy
(`Core.symex`, `Core.Fml.step`) runs as compiled code, its result is quoted
(`Core.Fml.quote`) and printed by `Core.Delab`'s printer, as today's are.
`#wp` also prints the reduction of the result's erasure (`Core.Fml.erase`)
when it is in `sol_decide`'s fragment, and `#step` the rule today's strategy
fires on the erasure, which is the rule the scoped strategy fires
(`docs/intrinsic.md`, M6a).

Each command is a second elaborator of today's syntax: it takes a scoped
formula and leaves any other term to today's.
-/

namespace Solidity.Tools

open Lean Elab Command Term Meta
open Semantics Decide

variable {C : Contract}

/-- What `#wp` shows of a scoped `φ`: the formula the scoped strategy leaves,
quoted, and the reduction of its erasure when it is in the fragment. -/
def wpQuotedC [FreshNames] (c : Lean.Expr) {Γ : Core.Ctx} (φ : Core.Fml C Γ) :
    Lean.Expr × Option String :=
  let ψ := Core.symex 200 φ
  let ψ' := ψ.erase []
  (ψ.quote c, if ψ'.inL Sym.empty then some (LFml.fmt ψ'.reduce) else none)

/-- What `#step` shows of a scoped `φ`: the formula one step leaves, quoted,
and `φ`'s erasure quoted, whose rule names the step. -/
def stepQuotedC (c : Lean.Expr) {Γ : Core.Ctx} (φ : Core.Fml C Γ) :
    Option Lean.Expr × Lean.Expr :=
  (φ.step.map (·.quote c), (φ.erase []).quote c)

/-- A closed scoped formula of a named contract: the formula, and the
contract's name quoted. -/
def elabCoreFormula? (t : Lean.Term) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  -- today's notation (`dl!{ … }`, `dl[C]{ … }`) is today's elaborator's,
  -- left unread so that it is not elaborated twice
  if let some (.atom _ v) := t.raw.getHead? then
    if v.startsWith "dl" then return none
  let φ ← try elabTerm t none catch _ => return none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Core.Fml 2 do return none
  let some n := (← whnfR ty.appFn!.appArg!).constName? | return none
  if φ.hasFVar || φ.hasMVar then throwError "the formula is not closed{indentExpr φ}"
  return some (φ, mkApp2 (mkConst ``Lean.mkConst) (toExpr n)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Lean.Level)))

/-- `#wp φ` for a scoped formula. -/
@[command_elab Solidity.Tools.«command#wp_»]
def elabWpCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | throwUnsupportedSyntax
  let e ← mkAppM ``wpQuotedC #[c, φ]
  let (ψ, red) ← unsafe evalExpr (Lean.Expr × Option String) (← inferType e) e
  let tail := match red with
    | some r => m!"\nupdate-free:\n    {r}"
    | none => m!"\noutside `sol_decide`'s fragment (`Fml.inL`): no reduction"
  logInfo (m!"symbolic execution leaves:\n    {ψ}" ++ tail)

/-- `#step φ` for a scoped formula. -/
@[command_elab Solidity.Tools.«command#step_»]
def elabStepCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | throwUnsupportedSyntax
  let e ← mkAppM ``stepQuotedC #[c, φ]
  let (ψ?, φ') ← unsafe evalExpr (Option Lean.Expr × Lean.Expr) (← inferType e) e
  match ψ? with
  | none => logInfo "no modality left: `close`"
  | some ψ =>
    let r := match ← Chain.ruleOfLine φ' with
      | some (_, n) => toString n
      | none => "?"
    logInfo m!"  ~[{r}]~>\n    {ψ}"

end Solidity.Tools
