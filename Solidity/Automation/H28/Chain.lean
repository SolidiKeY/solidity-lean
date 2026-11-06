import Solidity.Automation.H28.Context
import Solidity.Calculus.RewriteChains
import Lean.Elab.Tactic.Basic

/-!
# Opt-in code generation for `sol_chain`

Use alongside the imports that already provide the desired chain elaborator.
Delegate original syntax and preserve its refusals and proof checks. The scoped
compiler Boolean and reader transform are shared with the opt-in prove helper.
-/

open Lean Elab Tactic

namespace Solidity.Automation.H28

/-- Opt into evaluator code generation while elaborating the original chain. -/
syntax (name := tacticSolH28Chain) "sol_h28_chain" : tactic

elab_rules : tactic
  | `(tactic| sol_h28_chain) => do
    let owner ← `(tactic| sol_chain)
    withTheReader Core.Context codegenContext (evalTactic owner)

end Solidity.Automation.H28
