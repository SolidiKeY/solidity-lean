import Lean
import Solidity.Frontend.ExpressionUniqueness.AxiomPins

/-! Verification tooling only: enumerate every imported owned kernel declaration,
including generated matchers, equation lemmas, constructors and instances.
Compiler extra-name metadata is recorded separately; final acceptance resolves
its overlap with the kernel declarations explicitly. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  unless env.header.modules.size == env.header.moduleData.size do
    throwError "module metadata arrays differ"
  for (entry, data) in env.header.modules.zip env.header.moduleData do
    let modName := entry.module
    if modName.toString.startsWith "Solidity.Frontend.ExpressionUniqueness." then
      let names := data.constants.map (fun ci => Json.str ci.name.toString)
      let owners ← data.constants.mapM fun ci => do
        let some idx := env.getModuleIdxFor? ci.name | throwError "kernel constant has no module owner"
        let some owner := env.header.modules[idx.toNat]? | throwError "kernel module owner index is invalid"
        pure (Json.mkObj [("name", Json.str ci.name.toString), ("owner", Json.str owner.module.toString)])
      let extras := data.extraConstNames.map (fun n => Json.str n.toString)
      let row := Json.mkObj [("module", Json.str modName.toString),
        ("constants", Json.arr names), ("ownership", Json.arr owners), ("codegen_extra", Json.arr extras)]
      logInfo m!"OWNED_KERNEL_MODULE {row.compress}"
