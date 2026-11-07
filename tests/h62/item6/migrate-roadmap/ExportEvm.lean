import Lean
import Solidity.Roadmap.Evm

/-! Read-only elaborated declaration inventory, including compiler-generated constants.
Debug types are version-specific fingerprints, not a proof of cross-version equality. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let rows : Array (Name × ConstantInfo × Name) := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some i =>
      let modName := env.header.moduleNames[i.toNat]!
      if modName.toString.startsWith "Solidity.Roadmap." then acc.push (n, ci, modName) else acc
    | none => acc
  let rows := rows.qsort fun a b => a.1.toString < b.1.toString
  for (name, info, modName) in rows do
    let axioms ← if info.isTheorem then collectAxioms name else pure #[]
    let row := Json.mkObj [
      ("module", toJson modName.toString),
      ("name", toJson name.toString),
      ("type_debug", toJson (toString info.type)),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("is_theorem", toJson info.isTheorem),
      ("is_unsafe", toJson info.isUnsafe),
      ("theorem_axioms", toJson (axioms.map Name.toString))]
    logInfo m!"ROADMAP_API {row.compress}"
  logInfo m!"ROADMAP_API_COUNT {rows.size}"
