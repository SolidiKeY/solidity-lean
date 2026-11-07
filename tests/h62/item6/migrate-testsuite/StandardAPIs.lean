import Lean

/- Isolated reproduction of the exact kernel refusal classifier used by
TestSuite/MemoryLoopReplay/Refusals.lean. This is an API/negative control,
not validation of the imported Solidity obligations. No budget override. -/
open Lean Meta

private def kernelTypingRefusal (action : MetaM Unit) : MetaM Bool :=
    withOptions (fun o => o.setBool `pp.raw true) do
  try
    action
    return false
  catch e =>
    let text ← e.toMessageData.toString
    if text.startsWith "(kernel)" && (text.splitOn "type mismatch").length > 1 then
      return true
    throw e

run_elab do
  let goodType := mkConst ``True
  let goodValue := mkConst ``True.intro
  let good ← withOptions (Elab.async.set · false) <| mkAuxLemma [] goodType goodValue
  unless (← getEnv).contains good do throwError "missing valid kernel lemma"
  let refused ← kernelTypingRefusal do
    let _ ← withOptions (Elab.async.set · false) <|
      mkAuxLemma [] (mkConst ``False) goodValue
    pure ()
  unless refused do throwError "false kernel lemma accepted"
  let unchanged ← kernelTypingRefusal (pure ())
  if unchanged then throwError "success classified as kernel refusal"

run_elab do
  for message in ["fixture type mismatch", "(kernel) fixture other error"] do
    let propagated ← try
      let _ ← kernelTypingRefusal (throwError message)
      pure false
    catch e => pure ((← e.toMessageData.toString) == message)
    unless propagated do throwError "non-refusal error was swallowed"

-- APIs referenced by the scoped replay negative controls.
#check Lean.tryCatchRuntimeEx
#check Lean.Elab.Term.elabTerm
#check Lean.Meta.mkEqRefl
#check Lean.Expr.getAppArgs
#check Lean.Expr.isAppOf
