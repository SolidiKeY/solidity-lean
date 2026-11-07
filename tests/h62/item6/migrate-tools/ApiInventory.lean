import Lean
import Lean.Util.CollectAxioms
import Solidity.Tools.CallFunctionShare
import Solidity.Tools.Common
import Solidity.Tools.CompleteVerification
import Solidity.Tools.Counterexample
import Solidity.Tools.CreationTryReplay
import Solidity.Tools.DiffTest
import Solidity.Tools.DirectArithmetic
import Solidity.Tools.DirectRuntime
import Solidity.Tools.Elementary
import Solidity.Tools.EntryReturn
import Solidity.Tools.Inspect
import Solidity.Tools.Latex
import Solidity.Tools.LatexSolkey
import Solidity.Tools.LatexTerm
import Solidity.Tools.LazyStorage
import Solidity.Tools.LeafArithmetic
import Solidity.Tools.LibraryTryReplay
import Solidity.Tools.PaymentReplay
import Solidity.Tools.Preconditions
import Solidity.Tools.ProgramTrace
import Solidity.Tools.ProofTree
import Solidity.Tools.QueryArithmetic
import Solidity.Tools.Run
import Solidity.Tools.Show
import Solidity.Tools.SolCases
import Solidity.Tools.SourceCounterexample
import Solidity.Tools.Taclet
import Solidity.Tools.Upstream
import Solidity.Tools.UpstreamEntry
import Solidity.Tools.Verify

/-! Read-only checked-environment inventory for the assigned Tools modules.
No theorem or axiom is added. Generated/private constants are included;
source theorem candidates are matched separately. Both their axiom union and
the union for every theorem-kind constant in each module are recorded.
-/
namespace H62.ToolsMigrationInventory
open Lean Elab Command

private def lastPart : Name → String
  | .str _ value => value
  | _ => ""

private def snapshot (moduleName : String) (wantedTheorems : List String) : CommandElabM Unit := do
  let environment ← getEnv
  let mut declarations : Array Json := #[]
  let mut sourceTheorems : Array Name := #[]
  let mut moduleTheorems : Array Name := #[]
  for (name, information) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    unless environment.header.moduleNames[index.toNat]!.toString == moduleName do continue
    let theoremKind := wasOriginallyTheorem environment name
    if theoremKind then moduleTheorems := moduleTheorems.push name
    declarations := declarations.push (Json.mkObj [
      ("name", toJson name.toString),
      ("type_expr", toJson (reprStr information.type)),
      ("level_params", toJson (information.levelParams.map Name.toString)),
      ("is_unsafe", toJson information.isUnsafe),
      ("is_theorem", toJson theoremKind)])
    if theoremKind && wantedTheorems.contains (lastPart name) then
      sourceTheorems := sourceTheorems.push name
  for expected in wantedTheorems do
    unless sourceTheorems.any (fun name => lastPart name == expected) do
      throwError "missing source theorem {moduleName}.{expected}"
  unless sourceTheorems.size == wantedTheorems.length do
    throwError "ambiguous source theorem mapping for {moduleName}"
  let collection : CollectAxioms.M Unit := sourceTheorems.forM CollectAxioms.collect
  let (_, state) := (collection.run environment).run {}
  let allCollection : CollectAxioms.M Unit := moduleTheorems.forM CollectAxioms.collect
  let (_, allState) := (allCollection.run environment).run state
  liftIO <| IO.println (Json.mkObj [
    ("module", toJson moduleName),
    ("declarations", toJson declarations),
    ("source_theorems", toJson (sourceTheorems.map Name.toString)),
    ("source_theorem_axiom_union", toJson (state.axioms.map Name.toString)),
    ("module_theorems", toJson (moduleTheorems.map Name.toString)),
    ("module_theorem_axiom_union", toJson (allState.axioms.map Name.toString))]).compress

run_cmd snapshot "Solidity.Tools.CallFunctionShare" []
run_cmd snapshot "Solidity.Tools.Common" []
run_cmd snapshot "Solidity.Tools.CompleteVerification" []
run_cmd snapshot "Solidity.Tools.Counterexample" ["liftV?_get", "lift?_spec", "runFramesF_approx", "eval3C_sound", "eval3_eq", "eval3_sound", "eval3_tt", "eval3_ff", "peel_eq", "not_holds_of_peelC", "not_valid_of_eval3Peel", "not_valid_of_peel", "not_holds_imp_of_eval3", "not_holds_imp_of_not_holds", "holds_and_intro", "not_of_not_valid"]
run_cmd snapshot "Solidity.Tools.CreationTryReplay" []
run_cmd snapshot "Solidity.Tools.DiffTest" []
run_cmd snapshot "Solidity.Tools.DirectArithmetic" ["boundedWalk_closed"]
run_cmd snapshot "Solidity.Tools.DirectRuntime" []
run_cmd snapshot "Solidity.Tools.Elementary" []
run_cmd snapshot "Solidity.Tools.EntryReturn" ["admitted_arguments", "admitted_result", "original_declaration", "function_marker_refused", "returnType_function", "function_arguments_refused"]
run_cmd snapshot "Solidity.Tools.Inspect" []
run_cmd snapshot "Solidity.Tools.Latex" []
run_cmd snapshot "Solidity.Tools.LatexSolkey" []
run_cmd snapshot "Solidity.Tools.LatexTerm" []
run_cmd snapshot "Solidity.Tools.LazyStorage" ["allB_rep", "allB_cons_true", "allB_arrayOf_rep", "holds_wt_of"]
run_cmd snapshot "Solidity.Tools.LeafArithmetic" []
run_cmd snapshot "Solidity.Tools.LibraryTryReplay" []
run_cmd snapshot "Solidity.Tools.PaymentReplay" []
run_cmd snapshot "Solidity.Tools.Preconditions" []
run_cmd snapshot "Solidity.Tools.ProgramTrace" []
run_cmd snapshot "Solidity.Tools.ProofTree" []
run_cmd snapshot "Solidity.Tools.QueryArithmetic" []
run_cmd snapshot "Solidity.Tools.Run" []
run_cmd snapshot "Solidity.Tools.Show" []
run_cmd snapshot "Solidity.Tools.SolCases" []
run_cmd snapshot "Solidity.Tools.SourceCounterexample" []
run_cmd snapshot "Solidity.Tools.Taclet" []
run_cmd snapshot "Solidity.Tools.Upstream" ["entryGuard_failed", "entryGuard_success", "entryGuard_prior", "readBytes_exact"]
run_cmd snapshot "Solidity.Tools.UpstreamEntry" []
run_cmd snapshot "Solidity.Tools.Verify" []

end H62.ToolsMigrationInventory
