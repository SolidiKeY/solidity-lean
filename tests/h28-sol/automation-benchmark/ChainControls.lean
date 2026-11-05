import Solidity.Examples.Chains.Storage
import Lean
import Solidity.Automation.H28.Chain

open Lean Elab Term Command Meta
set_option Elab.async false

elab "h28_type% " id:ident : term => do
  return (← getConstInfo id.getId).type

elab "#h28_mark " label:str : command => do
  let ticks ← IO.monoNanosNow
  let beats ← IO.getNumHeartbeats
  let budget := maxHeartbeats.get (← getOptions)
  logInfo m!"H28_MARK {label.getString} {ticks} {beats} {budget}"

elab "#h28_assert_exact " original:ident tested:ident : command => do
  let sourceInfo ← getConstInfo original.getId
  let testedInfo ← getConstInfo tested.getId
  unless testedInfo.type == sourceInfo.type do
    throwError "single-goal control changed the original theorem type"
  logInfo m!"H28_TYPE_OK {tested.getId}"

elab "#h28_assert_combine " left:ident right:ident tested:ident : command => do
  let leftInfo ← getConstInfo left.getId
  let rightInfo ← getConstInfo right.getId
  let testedInfo ← getConstInfo tested.getId
  unless testedInfo.type == mkApp2 (mkConst ``And) leftInfo.type rightInfo.type do
    throwError "benchmark changed the exact conjunction of the original theorem types"
  logInfo m!"H28_TYPE_OK {tested.getId}"


elab "h28_pointwise_pair% " id:ident : term => do
  let info ← getConstInfo id.getId
  return ← forallTelescope info.type fun args body =>
    mkForallFVars args (mkApp2 (mkConst (Name.str .anonymous "And")) body body)

elab "#h28_assert_pointwise " original:ident tested:ident : command => do
  let sourceInfo ← getConstInfo original.getId
  let testedInfo ← getConstInfo tested.getId
  let expected ← liftTermElabM do
    return ← forallTelescope sourceInfo.type fun args body =>
      mkForallFVars args (mkApp2 (mkConst (Name.str .anonymous "And")) body body)
  unless testedInfo.type == expected do
    throwError "pointwise control changed original binders or statement"
  logInfo m!"H28_TYPE_OK {tested.getId}"

elab "#h28_audit " id:ident : command => do
  let info ← getConstInfo id.getId
  let axioms ← collectAxioms id.getId
  let entries ← axioms.mapM fun axiomName => do
    let axiomInfo ← getConstInfo axiomName
    return Json.mkObj [("name", toJson axiomName.toString),
      ("signature", toJson (reprStr axiomInfo.type))]
  let payload := Json.mkObj [("name", toJson id.getId.toString),
    ("signature", toJson (reprStr info.type)),
    ("proof_nodes", toJson info.value!.sizeWithoutSharing),
    ("axioms", Json.arr entries)]
  logInfo m!"H28_AUDIT {payload.compress}"
  let ticks ← IO.monoNanosNow
  let beats ← IO.getNumHeartbeats
  liftTermElabM do
    addDecl <| Declaration.thmDecl {
      name := Name.str info.name "kernelReplay"
      levelParams := info.levelParams
      type := info.type
      value := info.value!
    }
  let ticksAfter ← IO.monoNanosNow
  let beatsAfter ← IO.getNumHeartbeats
  logInfo m!"H28_REPLAY {id.getId} {ticksAfter - ticks} {beatsAfter - beats}"





set_option trace.Elab.tactic.backtrack true
private def h28Options (opts : Lean.Options) : String :=
  s!"{opts.getBool `compiler.extract_closed true} {opts.getNat `maxHeartbeats 200000} {opts.getNat `maxRecDepth 1000} {opts.getBool `sol.prove.compiledPlain true} {opts.getBool `sol.prove.sharedResidues false}"
private def h28Observe : Lean.Elab.Tactic.Tactic := fun stx => do
  trace[Elab.tactic.backtrack] "H28_OWNER_OPTIONS {stx.getKind} {h28Options (← getOptions)}"
  let context ← readThe Lean.Core.Context
  liftM <| Lean.Core.liftIOCore <| IO.println s!"H28_OWNER_CONTEXT {context.maxHeartbeats} {context.maxRecDepth} {context.initHeartbeats} {context.diag} {context.initHeartbeats + context.maxHeartbeats} {context.options.getBool `compiler.extract_closed true}"
  throwUnsupportedSyntax
elab "#h28_codegen_outer" : command => do
  logInfo m!"H28_OUTER_OPTIONS {h28Options (← getOptions)}"
run_cmd do
  let stx ← `(tactic| sol_chain)
  let .ok command := Parser.runParserCategory (← getEnv) `command ("attribute [tactic " ++ stx.raw.getKind.toString ++ "] h28Observe") | throwError "observer attribute did not parse"
  elabCommand command
#h28_codegen_outer
#h28_mark "cold-start"
theorem benchmarkCold : h28_type% Solidity.Examples.Chains.Storage.AgeWrite.chain := by
  intro m φ
  sol_h28_chain
#h28_mark "cold-end"
#h28_codegen_outer
#h28_mark "warm-start"
theorem benchmarkWarm : h28_type% Solidity.Examples.Chains.Storage.AgeWrite.chain := by
  intro m φ
  sol_h28_chain
#h28_mark "warm-end"
#h28_assert_exact Solidity.Examples.Chains.Storage.AgeWrite.chain benchmarkCold
#h28_assert_exact Solidity.Examples.Chains.Storage.AgeWrite.chain benchmarkWarm
#h28_audit benchmarkCold
#h28_audit benchmarkWarm
#h28_audit Solidity.Examples.Chains.Storage.AgeWrite.chain

#h28_codegen_outer

#print axioms benchmarkCold
#print axioms benchmarkWarm
#print axioms Solidity.Examples.Chains.Storage.AgeWrite.chain
