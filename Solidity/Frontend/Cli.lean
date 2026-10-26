import Solidity.Frontend.Testing
import Solidity.Tools.Inspect
import Solidity.Tools.Run

/-!
Machine-readable inspection and concrete execution for the native CLI.
Requests are JSON data, never interpolated Lean programs. Verification uses
Testing's original obligations and kernel/axiom gate. Inspection is diagnostic;
an ordinary proof tree is refused for recursive or callback obligations.
-/

namespace Solidity.Frontend

open Lean Elab Command Term Meta
open Solidity.Tools

private def rowName (r : ImportRow) : String :=
  if r.sourceName.isEmpty then r.name else r.sourceName

private def rowSignature (r : ImportRow) : String :=
  if r.sourceSignature.isEmpty then s!"{rowName r}({",".intercalate (r.params.map Prod.snd)})"
  else r.sourceSignature

private def jsonInt (v : Json) : Except String Int := do
  if let .str s := v then
    let some n := s.toInt? | throw "expected a decimal integer"
    return n
  v.getInt?

private def rawArgument (v : Json) : Except String RawExpr := do
  if let .bool b := v then return .bool b
  let n ← jsonInt v
  return if n < 0 then .unop .neg (.num n.natAbs) else .num n.natAbs

private def runRequest [FreshNames] (C : Contract) (f : String) (request : Json) :
    Except String (List String) := do
  let args ← (← request.getObjValAs? (Array Json) "args").toList.mapM rawArgument
  let state ← request.getObjVal? "state"
  let integer (key : String) : Except String (Option Int) := do
    if let .ok v := state.getObjVal? key then return some (← jsonInt v)
    return none
  let sender ← integer "sender"
  let value ← integer "value"
  let timestamp ← integer "timestamp"
  let balance ← integer "balance"
  let mut σ ← State.withTx (State.init C) sender value timestamp balance
  if let some address ← integer "selfAddress" then
    if address < 0 || address ≥ 2 ^ 160 then throw "selfAddress must fit 160 bits"
    let some word := PrimTy.ofInt? .uint address | throw "invalid selfAddress"
    σ := { σ with tx := { σ.tx with selfAddress := word } }
  if let .ok storage := state.getObjVal? "storage" then
    for (name, v) in (← storage.getObj?).toList do
      let some T := Semantics.lookupBy name C.vars | throw s!"{name} is not a state variable"
      let v ← match T with
        | .prim .bool => pure (Semantics.CallValue.bool (← v.getBool?))
        | .prim p =>
          let some v := PrimTy.ofInt? p (← jsonInt v)
            | throw s!"{name}: value outside its model type"
          pure (.ofTyped v)
        | _ => throw s!"{name}: concrete CLI state supports primitive storage roots only"
      σ ← State.withRoot σ name v
  runReport C σ f args

private def inspectRequest (N : Lean.Name) (r : ImportRow) (tail : TailMode)
    (show_ : String) : CommandElabM (String × String × TailMode × Option Json) := do
  if show_ == "goals" then
    let (status, reason, mode) ← testObligation N r tail (showGoals := true)
    return (status, if reason.isEmpty then "No open goals." else reason, mode, none)
  liftTermElabM do
    let φ ← Symex.evaluable (← testFormula N r)
    let mode ← testTailMode N r tail φ
    let C : Expr := Lean.mkConst N
    let φ := if mode == .clean then mkAppN (mkConst ``Fml.imp) #[C, ctxE [],
      mkApp2 (mkConst ``Fml.cleanTail) C (ctxE []), φ] else φ
    if show_ == "tree" then
      unless ← testOrdinaryTree N φ do
        return ("unsupported", "proof-tree inspection requires a nonrecursive obligation without callbacks; use --show obligation or --show goals", mode, none)
      let tree ← ProofTree.ofFormula C φ
      let text ← (← tree.display).toString
      return ("inspected", text, mode, some (← tree.toJson))
    let contract ← unsafe evalExpr Contract (mkConst ``Contract) C
    let body ← unsafe evalExpr (Fml contract []) (← inferType φ) (← Symex.evaluable φ)
    let text ← if r.tag == .specified then body.show C []
      else sourceProblemText C N.getString! r.name body
    return ("inspected", text, mode, none)

syntax (name := solidityCli) "#solidity_cli " ident &" request " str &" to " str : command

@[command_elab solidityCli]
def elabSolidityCli : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let request ← ofExcept <| Json.parse (stx[3].isStrLit?.getD "")
  let action ← ofExcept <| request.getObjValAs? String "action"
  let show_ ← ofExcept <| request.getObjValAs? String "show"
  let only? := (request.getObjValAs? String "function").toOption
  let allRows ← reportRows N
  let rows := allRows.filter fun r => only?.all r.matchesSelector
  if rows.isEmpty then throwError "no functions selected"
  if action == "run" && rows.length != 1 then
    throwError "run requires exactly one function; select an overload by signature"
  let tail ← contractTailMode N allRows
  let output := stx[5].isStrLit?.getD ""
  let mut results : Array Json := rows.toArray.map fun r => Json.mkObj [
    ("function", toJson (rowName r)), ("signature", toJson (rowSignature r)),
    ("tag", toJson r.tag.toStr), ("status", toJson "notRun"),
    ("reason", toJson "contract run interrupted"), ("text", toJson ""),
    ("reading", toJson "solc"), ("elapsedMs", toJson (0 : Nat))]
  IO.FS.writeFile output (Json.arr results).pretty
  for r in rows, i in [:rows.length] do
    let start ← IO.monoMsNow
    let operation : CommandElabM (String × String × TailMode × Option Json) := do
        if r.status != .elaborated then return (r.status.toStr, r.reason, TailMode.solc, none)
        if action == "run" then
          if r.name == "constructor" then
            return ("unsupported", "use the Lean #deploy command for constructor execution", .solc, none)
          let lines ← liftTermElabM do
            let C ← unsafe evalExpr Contract (mkConst ``Contract) (mkConst N)
            ofExcept <| runRequest C r.name request
          let head := lines.headD "error"
          let status := if head == "ok" then "ok" else if head.startsWith "revert" then "revert"
            else if head.startsWith "panic" then "panic" else "diverge"
          return (status, "\n".intercalate lines, .solc, none)
        if r.tag == .skip || r.tag == .internal then return (r.tag.toStr, "no independent obligation", .solc, none)
        inspectRequest N r tail show_
    let (status, text, mode, tree) ← try operation
      catch e => pure ("error", ← e.toMessageData.toString, .solc, none)
    results := results.set! i <| Json.mkObj <| [
      ("function", toJson (rowName r)), ("signature", toJson (rowSignature r)),
      ("tag", toJson r.tag.toStr), ("status", toJson status),
      ("reason", toJson (if ["error", "unsupported", "excluded"].contains status then text else "")),
      ("text", toJson text), ("reading", toJson (if mode == .clean then "clean" else "solc")),
      ("elapsedMs", toJson ((← IO.monoMsNow) - start))] ++
      (tree.toList.map fun t => ("tree", t))
    IO.FS.writeFile output (Json.arr results).pretty

end Solidity.Frontend
