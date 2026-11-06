import Lean
import Solidity.Backend.PrimitivePackets.Constants.Controls

/-! Complete owned inventory plus the previously audited imported sword equation.
The defining module remains actual: imported continuity is not owned code. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut entries : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!
      if owner.toString.startsWith "Solidity.Backend.PrimitivePackets.Constants." ||
          name == ``Solidity.Evm.sword.eq_1 then
        let axioms ← Lean.collectAxioms name
        let signature ← liftTermElabM do
          withOptions (fun opts => (opts.setBool `pp.proofs true).setBool `pp.universes true) do
            return toString (← Lean.Meta.ppExpr info.type)
        let kind := match info with
          | .axiomInfo _ => r"axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        entries := entries.push (Json.mkObj [
          ("name", toJson name.toString), ("module", toJson owner.toString),
          ("kind", toJson kind), ("signature", toJson signature),
          ("levels", toJson (info.levelParams.map Name.toString)),
          ("isUnsafe", toJson info.isUnsafe), ("isPartial", toJson info.isPartial),
          ("axioms", toJson (axioms.map Name.toString).toList)])
  let mut root := System.FilePath.mk (← getFileName)
  for _ in [:4] do root := root.parent.getD "."
  liftIO <| IO.FS.writeFile (root / "tests/primitive-packets-1105/Constants/evidence/kernel-inventory.actual.json")
    (Json.pretty (Json.arr entries))
  logInfo m!"Constants audit: {entries.size} declarations recorded"

set_option pp.privateNames true in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]!.toString.startsWith
          "Solidity.Backend.PrimitivePackets.Constants." || name == ``Solidity.Evm.sword.eq_1 then
        names := names.push name
  for name in names.qsort Name.lt do
    elabCommand (← `(command| #print axioms $(mkIdent name)))
