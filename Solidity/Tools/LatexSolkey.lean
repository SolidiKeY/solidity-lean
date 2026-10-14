import Solidity.Tools.Latex
import Solidity.Calculus.ChainGen
import Solidity.Frontend.Problems

/-!
# A solkey function's obligation and derivation as LaTeX

`#latex_obligation N.f` prints the obligation of `N.f` (`statement?`, as
`#solkey_problem` reads it) as a math fragment; `#latex_derivation N.f`
prints the derivation the strategy finds from it, every step over its line.
The `_file` forms write the fragment to a path, as `scripts/latex-sol.sh` does.
`N` is a module `solc_import`ed as `N`.
-/

namespace Solidity.Latex

open Lean Elab Command

private def obligationOf (f : Ident) : CommandElabM Expr := do
  let some φ ← Solidity.Frontend.statement? f.getId.getPrefix f.getId
    | throwError "{f.getId} has no obligation"
  return φ

private def obligationLatex (f : Ident) : CommandElabM String := do
  let φ ← obligationOf f
  liftTermElabM do calculusLatex φ

private def derivationLatexOf (f : Ident) : CommandElabM String := do
  let φ ← obligationOf f
  liftTermElabM do
    let g ← Solidity.Chain.generate φ
    if let some note := g.stop then logWarning note
    derivationLatex φ g.links

elab "#latex_obligation " f:ident : command => do
  logInfo (← obligationLatex f)

elab "#latex_obligation_file " path:str f:ident : command => do
  IO.FS.writeFile path.getString ((← obligationLatex f) ++ "\n")

elab "#latex_derivation " f:ident : command => do
  logInfo (← derivationLatexOf f)

elab "#latex_derivation_file " path:str f:ident : command => do
  IO.FS.writeFile path.getString ((← derivationLatexOf f) ++ "\n")

end Solidity.Latex
