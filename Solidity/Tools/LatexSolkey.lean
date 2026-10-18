import Solidity.Tools.Latex
import Solidity.Calculus.ChainGen
import Solidity.Frontend.Problems

/-!
# A derivation, and a solkey function's obligation, as LaTeX

`#latex_derivation φ` prints the derivation the strategy finds from the
scoped formula `φ` (`Chain.generate`, as `#chain` writes it), presented as
the options say (`Tools/Latex.lean`); for an identifier `N.f` of a module
`solc_import`ed as `N`, from the obligation of `N.f` (`statement?`, as
`#solkey_problem` reads it), which `#latex_obligation N.f` prints.  The
`_file` forms write the fragment to a path, as `scripts/latex-sol.sh` does.
-/

namespace Solidity.Latex

open Lean Elab Command Meta

/-- A generated chain's steps: the strategy's, grouped as `#chain` groups
them when `groups` (`groupSteps`), then the rewrites, each with its `FmlRw`
(past the program only when `past`). -/
def genSteps (o : Options) (g : Chain.Gen) : Array Step :=
  let raw := g.steps.map fun (n, l, _) => (n, l)
  let strat : Array Step := if o.groups then
      (Chain.groupSteps raw).map fun (a, l) =>
        let r := if a.startsWith "~[" && a.endsWith "]~>" then (a.drop 2).dropRight 3
          else if a == "~*>" then "~*>" else ""
        { rule := r, line := l }
    else raw.map fun (n, l) => { rule := n, line := l }
  let rws := if g.rws.size == g.rewrites.size then g.rws.map some
    else g.rewrites.map fun _ => none
  let past : Array Step := if o.past then
      (g.rewrites.zip rws).map fun ((n, l, _), rw?) => { rule := n, line := l, rw? }
    else #[]
  strat ++ g.openRws.map (fun (n, l, _) => { rule := n, line := l }) ++ past

/-- The derivation from the scoped formula `φ`, a note logged where the
strategy stops early. -/
def derivationOf (o : Options) (φ : Expr) : TermElabM String := do
  let g ← Chain.generate φ (past := o.past)
  if let some note := g.stop then logWarning note
  derivationLatex φ (genSteps o g) o

/-- The obligation of `N.f`, if `f` names a function of a `solc_import`:
`N.f` as written, or in a namespace open around the command. -/
def obligation? (f : Lean.Name) : CommandElabM (Option Expr) := do
  let mut ns ← getCurrNamespace
  repeat
    let g := ns ++ f
    if (← getEnv).contains (g.getPrefix ++ `report) then
      return ← Solidity.Frontend.statement? g.getPrefix g
    if ns.isAnonymous then break
    ns := ns.getPrefix
  return none

private def obligationOf (f : Ident) : CommandElabM Expr := do
  let some φ ← obligation? f.getId | throwError "{f.getId} has no obligation"
  return φ

private def obligationLatex (o : Options) (f : Ident) : CommandElabM String := do
  let φ ← obligationOf f
  liftTermElabM do exprLatex φ o

/-- The derivation of `t`: an obligation's, if `t` names a solc function,
else the scoped formula `t`'s. -/
private def derivationLatexOf (o : Options) (t : Term) : CommandElabM String := do
  if let `($f:ident) := t then
    if let some φ ← obligation? f.getId then return ← liftTermElabM (derivationOf o φ)
  liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    derivationOf o (← instantiateMVars e)

/-- `#latex_obligation (opts) N.f`: the obligation of `N.f`. -/
elab "#latex_obligation " opts:latexOpt* f:ident : command => do
  logInfo (← obligationLatex (← liftCoreM (elabOpts opts)) f)

/-- `#latex_obligation_file "path" (opts) N.f`: write it. -/
elab "#latex_obligation_file " path:str opts:latexOpt* f:ident : command => do
  IO.FS.writeFile path.getString ((← obligationLatex (← liftCoreM (elabOpts opts)) f) ++ "\n")

/-- `#latex_derivation (opts) t`: the derivation from `N.f`'s obligation, or
from the scoped formula `t`. -/
elab "#latex_derivation " opts:latexOpt* t:term : command => do
  logInfo (← derivationLatexOf (← liftCoreM (elabOpts opts)) t)

/-- `#latex_derivation_file "path" (opts) t`: write it. -/
elab "#latex_derivation_file " path:str opts:latexOpt* t:term : command => do
  IO.FS.writeFile path.getString ((← derivationLatexOf (← liftCoreM (elabOpts opts)) t) ++ "\n")

end Solidity.Latex
