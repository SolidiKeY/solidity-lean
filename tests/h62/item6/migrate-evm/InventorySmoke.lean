-- Generated inventory-helper acceptance fixture
import Lean
import Solidity.Evm.Machine

open Lean

-- Raw expression representations retain exact elaborated types and levels.
-- Toolchain-generated auxiliaries are included; compare with source ownership.
#eval show CoreM Unit from do
  let env ← getEnv
  let entries := env.constants.toList.mergeSort (fun a b => decide (a.1.toString ≤ b.1.toString))
  for (name, info) in entries do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx]!.toString
    unless moduleName.startsWith "Solidity.Evm." do continue
    let kind : String := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let row := Json.mkObj [
      ("module", toJson moduleName), ("name", toJson name.toString),
      ("kind", toJson kind), ("type_repr", toJson (reprStr info.type)),
      ("level_params", toJson (info.levelParams.map Name.toString))]
    IO.println row.compress
