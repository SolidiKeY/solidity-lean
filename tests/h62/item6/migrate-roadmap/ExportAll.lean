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

/-! Kernel-checked legacy enum observations for comparison with the new fixture. -/

open Solidity.Roadmap.Evm in
#guard Fork.osaka.toCtorIdx == 0

open Solidity.Roadmap.Evm in
#guard Precompile.ecrecover.toCtorIdx == 0

open Solidity.Roadmap.Evm in
#guard Precompile.sha256.toCtorIdx == 1

open Solidity.Roadmap.Evm in
#guard Precompile.ripemd160.toCtorIdx == 2

open Solidity.Roadmap.Evm in
#guard Precompile.identity.toCtorIdx == 3

open Solidity.Roadmap.Evm in
#guard Precompile.modexp.toCtorIdx == 4

open Solidity.Roadmap.Evm in
#guard Precompile.bnAdd.toCtorIdx == 5

open Solidity.Roadmap.Evm in
#guard Precompile.bnMul.toCtorIdx == 6

open Solidity.Roadmap.Evm in
#guard Precompile.bnPairing.toCtorIdx == 7

open Solidity.Roadmap.Evm in
#guard Precompile.blake2f.toCtorIdx == 8

open Solidity.Roadmap.Evm in
#guard Precompile.pointEvaluation.toCtorIdx == 9

open Solidity.Roadmap.Evm in
#guard Precompile.blsG1Add.toCtorIdx == 10

open Solidity.Roadmap.Evm in
#guard Precompile.blsG1Msm.toCtorIdx == 11

open Solidity.Roadmap.Evm in
#guard Precompile.blsG2Add.toCtorIdx == 12

open Solidity.Roadmap.Evm in
#guard Precompile.blsG2Msm.toCtorIdx == 13

open Solidity.Roadmap.Evm in
#guard Precompile.blsPairing.toCtorIdx == 14

open Solidity.Roadmap.Evm in
#guard Precompile.blsMapFpToG1.toCtorIdx == 15

open Solidity.Roadmap.Evm in
#guard Precompile.blsMapFp2ToG2.toCtorIdx == 16

open Solidity.Roadmap.Evm in
#guard Precompile.p256Verify.toCtorIdx == 17
