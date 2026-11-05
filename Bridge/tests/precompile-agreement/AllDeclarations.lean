import SolidityBridge.PrecompileAgreement.Controls
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    let text := name.toString
    if text.startsWith "SolidityBridge.PrecompileAgreement." ||
        text.startsWith "_private.SolidityBridge.PrecompileAgreement." then
      let axioms ← collectAxioms name
      unless axioms.all (fun n => [``propext, ``Classical.choice, ``Quot.sound].contains n) do
        throwError "nonstandard axiom in {name}: {axioms}"
      logInfo m!"AXIOM {name}: {axioms}"
      count := count + 1
  if count = 0 then throwError "empty declaration audit"
  logInfo m!"ALL_DECLARATIONS_PASS count={count}"
