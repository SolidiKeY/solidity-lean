import Solidity.Automation.H28.Context
import Solidity.Calculus.TacticSyntax
import Lean.Elab.Tactic.Basic

/-!
# Opt-in code generation for `sol_prove`

Use alongside the imports that already provide the desired `sol_prove` owner.
Each goal is recomputed by that original tactic. Only closed-term extraction
while compiling evaluator helpers is disabled; typing, kernel checking,
owner refusals and step bounds remain with the owner. No default is changed.
-/

open Lean Elab Tactic

namespace Solidity.Automation.H28

/-- Opt into evaluator code generation with closed-term extraction disabled. -/
syntax (name := tacticSolH28Prove) "sol_h28_prove"
  ("(" &"steps" ":=" num ")")? : tactic

elab_rules : tactic
  | `(tactic| sol_h28_prove $[(steps := $steps:num)]?) => do
    let owner ← `(tactic| sol_prove $[(steps := $steps:num)]?)
    withTheReader Core.Context codegenContext (evalTactic owner)

end Solidity.Automation.H28
