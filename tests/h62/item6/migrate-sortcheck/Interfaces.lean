import Solidity.SortCheck.Faithfulness
import Solidity.SortCheck.Parser
import Lean.Util.CollectAxioms

/-! Complete elaborated declaration census for all three imported modules,
including generated/internal declarations. Output is evidence, not a proof
of cross-toolchain definitional equality. Whole-source hashes freeze source.
Do not register this test as a core library module. -/
open Lean Elab Command Meta
set_option pp.all true
set_option pp.universes true
run_cmd do
  let env ← getEnv
  let modules := #[`Solidity.SortCheck.Annotations, `Solidity.SortCheck.Parser,
    `Solidity.SortCheck.Faithfulness]
  let ids := modules.map fun m => (env.getModuleIdx? m).get!
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if (env.getModuleIdxFor? n).any ids.contains then acc.push n else acc
  let names := names.qsort fun a b => a.toString < b.toString
  logInfo m!"DECLARATION_COUNT {names.size}"
  for n in names do
    let info := (env.find? n).get!
    let ty ← liftTermElabM <| ppExpr info.type
    let axioms ← collectAxioms n
    logInfo m!"DECLARATION {n}\nTYPE {ty}\nAXIOMS {axioms}"
