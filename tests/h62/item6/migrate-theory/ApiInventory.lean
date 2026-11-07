import Lean
import Solidity.Theory.Bridge.Denote
import Solidity.Theory.CallerModel.Static
import Solidity.Theory.Mutability.Assignable
import Solidity.Theory.Mutability.Closer
import Solidity.Theory.Mutability.Payable
import Solidity.Theory.Mutability.Pure
import Solidity.Theory.Mutability.View
import Solidity.Theory.Progress.Calls
import Solidity.Theory.Progress.Controls
import Solidity.Theory.Progress.Fragment
import Solidity.Theory.Progress.Leaves
import Solidity.Theory.Progress.Outcome
import Solidity.Theory.Progress.Program
import Solidity.Theory.Progress.Tuple
import Solidity.Theory.Reachable.CallerModel
import Solidity.Theory.Reachable.CleanTail
import Solidity.Theory.Reachable.Mode
import Solidity.Theory.Segs
import Solidity.Theory.Typed.Leaves
import Solidity.Theory.Typed.Mem
import Solidity.Theory.Typed.MemMirror
import Solidity.Theory.Typed.Obs
import Solidity.Theory.Typed.Obs.Ops
import Solidity.Theory.Typed.Obs.Paths
import Solidity.Theory.Typed.Obs.Values

/-! Read-only introspection of imported Theory declarations and their axiom
closures. This adds no production declarations or trust assumptions. -/
open Lean Elab Command

private def exportTheoryModule (mod : Name) : CommandElabM Unit := do
  let env : Environment ← getEnv
  let some target := env.getModuleIdx? mod | throwError "missing module {mod}"
  let entries : List (Name × ConstantInfo) := env.constants.toList.filter
    (fun entry => env.getModuleIdxFor? entry.1 == some target)
  liftIO <| IO.println ("H62_API_MODULE " ++ (Json.mkObj
    [("module", toJson mod.toString), ("count", toJson entries.length)]).compress)
  for (name, info) in entries do
    let axioms : Array Name ← Lean.collectAxioms name
    let kind : String := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let row : Json := Json.mkObj [("module", toJson mod.toString),
      ("name", toJson name.toString), ("kind", toJson kind),
      ("level_params", toJson (info.levelParams.map (fun n => n.toString))),
      ("raw_type_expr", toJson (reprStr info.type)),
      ("axioms", toJson (axioms.map (fun n => n.toString)))]
    liftIO <| IO.println ("H62_API_JSON " ++ row.compress)

run_cmd exportTheoryModule `Solidity.Theory.Bridge.Denote

run_cmd exportTheoryModule `Solidity.Theory.CallerModel.Static

run_cmd exportTheoryModule `Solidity.Theory.Mutability.Assignable

run_cmd exportTheoryModule `Solidity.Theory.Mutability.Closer

run_cmd exportTheoryModule `Solidity.Theory.Mutability.Payable

run_cmd exportTheoryModule `Solidity.Theory.Mutability.Pure

run_cmd exportTheoryModule `Solidity.Theory.Mutability.View

run_cmd exportTheoryModule `Solidity.Theory.Progress.Calls

run_cmd exportTheoryModule `Solidity.Theory.Progress.Controls

run_cmd exportTheoryModule `Solidity.Theory.Progress.Fragment

run_cmd exportTheoryModule `Solidity.Theory.Progress.Leaves

run_cmd exportTheoryModule `Solidity.Theory.Progress.Outcome

run_cmd exportTheoryModule `Solidity.Theory.Progress.Program

run_cmd exportTheoryModule `Solidity.Theory.Progress.Tuple

run_cmd exportTheoryModule `Solidity.Theory.Reachable.CallerModel

run_cmd exportTheoryModule `Solidity.Theory.Reachable.CleanTail

run_cmd exportTheoryModule `Solidity.Theory.Reachable.Mode

run_cmd exportTheoryModule `Solidity.Theory.Segs

run_cmd exportTheoryModule `Solidity.Theory.Typed.Leaves

run_cmd exportTheoryModule `Solidity.Theory.Typed.Mem

run_cmd exportTheoryModule `Solidity.Theory.Typed.MemMirror

run_cmd exportTheoryModule `Solidity.Theory.Typed.Obs

run_cmd exportTheoryModule `Solidity.Theory.Typed.Obs.Ops

run_cmd exportTheoryModule `Solidity.Theory.Typed.Obs.Paths

run_cmd exportTheoryModule `Solidity.Theory.Typed.Obs.Values
