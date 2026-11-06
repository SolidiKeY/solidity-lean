import Lean
import Solidity.Roadmap.Contracts
import Solidity.Roadmap.Controls
import Solidity.Roadmap.Evm
import Solidity.Roadmap.Frontend
import Solidity.Roadmap.TypedRun
import Solidity.Roadmap.V16.CreationLibrarySpec
import Solidity.Roadmap.V16.CreationReturnConsumer
import Solidity.Roadmap.V16.H24Input
import Solidity.Roadmap.V16.NativeParentConsumer
import Solidity.Roadmap.V16.NativeRevertConsumer
import Solidity.Roadmap.V16.RelationalGuardSpec
import Solidity.Roadmap.V16.SSCP2.NewAllocation
import Solidity.Roadmap.V16.SSCP2.NewAllocationControls
import Solidity.Roadmap.V16.SourceSizeControls
import Solidity.Roadmap.V16.SourceTransactionConsumer

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
