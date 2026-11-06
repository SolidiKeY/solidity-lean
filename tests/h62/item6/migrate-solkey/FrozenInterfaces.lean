import Solidity.Solkey.ComputedRevert
import Solidity.Solkey.Constructors
import Solidity.Solkey.QuantifiedDiamond
import Solidity.Solkey.ScopedFlip
import Solidity.Solkey.TestSuite
import Lean.Util.CollectAxioms

/-! Off-root migration inventory. Every constant belonging to one of the five
assigned modules is included, including command-generated and private constants.
Types are recorded as kernel expressions, without pretty-printer resolution.
This command adds no theorem, axiom, or changed proof budget. The output is
bulk evidence and belongs outside Git. Expression-representation differences
must be investigated; they do not authorize changing a frozen statement. -/
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let modules : List Name := [
    `Solidity.Solkey.ComputedRevert, `Solidity.Solkey.Constructors,
    `Solidity.Solkey.QuantifiedDiamond, `Solidity.Solkey.ScopedFlip,
    `Solidity.Solkey.TestSuite]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[index.toNat]! then
        if let .axiomInfo _ := info then
          throwError "module-owned axiom declaration: {name}"
        if info.isTheorem then
          let axioms ← Lean.collectAxioms name
          let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
          unless axioms.all allowed.contains do
            throwError "forbidden axiom dependency in {name}: {axioms}"
  let entries := env.constants.toList.filterMap fun (name, info) => do
    let index ← env.getModuleIdxFor? name
    let owner := env.header.moduleNames[index.toNat]!
    if !modules.contains owner then none else
      let kind : String := match info with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      some (name.toString, Json.mkObj [
        ("kind", toJson kind),
        ("name", toJson name.toString),
        ("module", toJson owner.toString),
        ("isTheorem", toJson info.isTheorem),
        ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("typeExpr", toJson (reprStr info.type)),
        ("valueExpr", toJson ((info.value? (allowOpaque := true)).map (fun value => reprStr value)))])
  for module in modules do
    unless env.constants.toList.any (fun (name, _) =>
        (env.getModuleIdxFor? name).any fun index =>
          env.header.moduleNames[index.toNat]! == module) do
      throwError "assigned module has no inventoried constants: {module}"
  for required in ["counterDeploy", "Solkey.EtherWallet.constructor.proved",
      "Solkey.ScopedFlip.additionStorageWrite.proved"] do
    unless entries.any (fun entry => entry.1 == required) do
      throwError "missing frozen theorem: {required}"
  let sorted := entries.toArray.qsort fun a b => a.1 < b.1
  liftIO <| IO.println (Json.arr (sorted.map Prod.snd)).compress

#print axioms counterDeploy
#print axioms Solkey.EtherWallet.constructor.proved
#print axioms Solkey.ScopedFlip.additionStorageWrite.proved
