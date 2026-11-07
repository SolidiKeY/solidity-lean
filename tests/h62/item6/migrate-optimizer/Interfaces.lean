import Lean
import Solidity.Optimizer.Controls

/-! Migration audit only: explicit kernel type expressions, including generated
structure API. This imports Lean only in the additive test scope. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter
    (fun n => n.toString.startsWith "Solidity.Optimizer.")
  for name in names.mergeSort (fun a b => a.toString ≤ b.toString) do
    if let some info := env.find? name then
      logInfo m!"INTERFACE {name} universes={repr info.levelParams}: {repr info.type}"

#print axioms Solidity.Optimizer.guardedPipeline_preserves
#print axioms Solidity.Optimizer.Preserves.pipeline
#print axioms Solidity.Optimizer.Pass.pipeline_append
#print axioms Solidity.Optimizer.beforeCompilation
