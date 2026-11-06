import Solidity.Solkey.ComputedRevert
import Solidity.Solkey.Constructors
import Solidity.Solkey.QuantifiedDiamond
import Solidity.Solkey.ScopedFlip
import Solidity.Solkey.TestSuite

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
  let entries := env.constants.toList.filterMap fun (name, info) => do
    let index ← env.getModuleIdxFor? name
    let owner := env.header.moduleNames[index.toNat]!
    if !modules.contains owner then none else
      some (name.toString, Json.mkObj [
        ("name", toJson name.toString),
        ("module", toJson owner.toString),
        ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("typeExpr", toJson (reprStr info.type))])
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
