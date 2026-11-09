import Solidity.Theory.Typed.Obs
import Solidity.Theory.Typed.Obs.Paths
import Solidity.Theory.Typed.Obs.Values
import Solidity.Theory.Typed.Obs.Ops
import Solidity.Theory.Typed.Mem
import Solidity.Theory.Typed.MemMirror
import Solidity.Theory.Typed.Leaves
import Solidity.Theory.Segs
import Solidity.Theory.Bridge.Denote
import Solidity.Theory.Mutability.View
import Solidity.Theory.Mutability.Pure
import Solidity.Theory.Mutability.Payable
import Solidity.Theory.Mutability.Assignable
import Solidity.Theory.Mutability.Closer
import Solidity.Theory.Progress.Outcome
import Solidity.Theory.Progress.Tuple
import Solidity.Theory.Progress.Fragment
import Solidity.Theory.Progress.Calls
import Solidity.Theory.Progress.Leaves
import Solidity.Theory.Progress.Program
import Solidity.Theory.Progress.Controls
import Solidity.Theory.CallerModel.Static
import Solidity.Theory.Reachable.Mode
import Solidity.Theory.Reachable.CleanTail
import Solidity.Theory.Reachable.CallerModel
import Lean

/-!
Elaborated frozen-theorem census. Bulk JSON is written only to the explicit
H62_AUDIT_CENSUS_OUT path. Includes generated theorem constants for reconciliation;
source declarations and private names are reconciled by the companion verifier.
No theorem is marked satisfiable by this metaprogram.
-/
open Lean Lean.Elab Lean.Elab.Command Lean.Meta
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true

run_cmd do
  let auditStarted ← liftIO IO.monoNanosNow
  let env ← getEnv
  let modules : Array String := #[ "Solidity.Theory.Typed.Obs", "Solidity.Theory.Typed.Obs.Paths", "Solidity.Theory.Typed.Obs.Values", "Solidity.Theory.Typed.Obs.Ops", "Solidity.Theory.Typed.Mem", "Solidity.Theory.Typed.MemMirror", "Solidity.Theory.Typed.Leaves", "Solidity.Theory.Segs", "Solidity.Theory.Bridge.Denote", "Solidity.Theory.Mutability.View", "Solidity.Theory.Mutability.Pure", "Solidity.Theory.Mutability.Payable", "Solidity.Theory.Mutability.Assignable", "Solidity.Theory.Mutability.Closer", "Solidity.Theory.Progress.Outcome", "Solidity.Theory.Progress.Tuple", "Solidity.Theory.Progress.Fragment", "Solidity.Theory.Progress.Calls", "Solidity.Theory.Progress.Leaves", "Solidity.Theory.Progress.Program", "Solidity.Theory.Progress.Controls", "Solidity.Theory.CallerModel.Static", "Solidity.Theory.Reachable.Mode", "Solidity.Theory.Reachable.CleanTail", "Solidity.Theory.Reachable.CallerModel" ]
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    match info with
    | .thmInfo _ =>
      if let some idx := env.getModuleIdxFor? name then
        let moduleName := env.header.moduleNames[idx.toNat]!.toString
        if modules.contains moduleName then
          let row ← liftTermElabM do
            let signature ← ppExpr info.type
            let (binders, conclusion) ← forallTelescope info.type fun xs conclusion => do
              let mut binders : Array Json := #[]
              for x in xs do
                let d ← x.fvarId!.getDecl
                let ty ← ppExpr d.type
                let prop ← isProp d.type
                binders := binders.push <| Json.mkObj [
                  ("name", toJson d.userName.toString),
                  ("binder_info", toJson (reprStr d.binderInfo)),
                  ("type", toJson ty.pretty), ("is_prop", toJson prop)]
              pure (binders, (← ppExpr conclusion).pretty)
            pure <| Json.mkObj [("name", toJson name.toString),
              ("module", toJson moduleName), ("signature", toJson signature.pretty),
              ("type_expr", toJson (reprStr info.type)),
              ("binders", Json.arr binders), ("conclusion", toJson conclusion)]
          rows := rows.push row
    | _ => pure ()
  let auditExtracted ← liftIO IO.monoNanosNow
  let some path ← liftIO (IO.getEnv "H62_AUDIT_CENSUS_OUT")
    | throwError "H62_AUDIT_CENSUS_OUT is required (absolute off-Git output path)"
  let target : System.FilePath := ⟨path⟩
  unless target.isAbsolute do
    throwError "Census output must be absolute"
  let cwd ← liftIO <| IO.FS.realPath (← IO.currentDir)
  unless (← liftIO <| (cwd / ".git").pathExists) do
    throwError "Run from the repository root"
  let some parent := target.parent | throwError "Census output needs a parent directory"
  let parent ← liftIO <| IO.FS.realPath parent
  if cwd.components.isPrefixOf parent.components then
    throwError "Census output must be outside the checkout"
  if ← liftIO target.pathExists then
    let actual ← liftIO <| IO.FS.realPath target
    if cwd.components.isPrefixOf actual.components then
      throwError "Census output symlink must not target the checkout"
  let auditPayload := (Json.arr rows).compress ++ "\n"
  let auditRendered ← liftIO IO.monoNanosNow
  liftIO <| IO.FS.writeFile path auditPayload
  let auditWritten ← liftIO IO.monoNanosNow
  logInfo m!"H62_CENSUS_STAGES extraction_ns={auditExtracted - auditStarted} serialization_ns={auditRendered - auditExtracted} write_ns={auditWritten - auditRendered}"
  logInfo m!"H62_ELABORATED_CENSUS: {rows.size} theorem constants; no witness claims"
