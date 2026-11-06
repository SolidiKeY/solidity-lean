import Solidity.Frontend.LiteralGrammarH28.WordTable

/-! # Generated proof-tactic declaration safety and kernel axiom report -/
open Lean in
run_cmd do
  let env ← getEnv
  let owner := env.getModuleIdxFor? `Solidity.Frontend.LiteralGrammarH28.wordNonliteral
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == owner then
      match info with
      | .defnInfo d => logInfo m!"DECL_SAFETY {name}: {repr d.safety}"
      | _ => pure ()
#print axioms Solidity.Frontend.LiteralGrammarH28.solWordTable_nonliteral
