import Solidity.Tools.DirectRuntime
import Solidity.Semantics.RunFuel

/-! Guards H90 narrow-local semantic regressions: checked overflow must abort through the existing model range guard,
unchecked unsigned/signed arithmetic must wrap, tuple assignment must capture
RHS values simultaneously, and parameter/storage refusals must remain. Finite
model executions and trusted checker observations are not solc source adequacy
proofs, native closure evidence or Lean proof certificates. The standalone
range guard currently reverts, while solc checked overflow carries Panic(0x11);
that inherited failure-payload adequacy gap is not repaired here. -/
namespace NarrowLocalRuntimeControls
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
private def sample (C : Contract) (formula : Fml C []) : IO String := do
  match formula with
  | .imp _ (.imp _ (.modal .diamond program _ _)) =>
    match Prog.runF 64 program (State.init C) with
    | .ok _ => pure "normal"
    | .error .panic => pure "panic"
    | .error .revert => pure "revert"
    | .error e => throw (IO.userError s!"unexpected halt {repr e}")
  | _ => throw (IO.userError "unexpected narrow obligation shape")
#eval show IO Unit from do
  let packet ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/h90/NarrowLocalRuntime.ast.json"))
  let some source := (J.nodes packet).find? (fun j => J.str? j "name" == some "NarrowLocalRuntime") |
    throw (IO.userError "missing narrow-local fixture")
  let base ← checked (contract executableReader source)
  for (name, halt) in [("assignment", "normal"), ("checkedOverflow", "revert"),
      ("uncheckedWrap", "normal"), ("signedOverflow", "revert"),
      ("signedWrap", "normal"), ("tupleSwap", "normal"), ("tupleRepeat", "normal"),
      ("tupleRepeatWrong", "panic"), ("narrowShadow", "normal")] do
    let some ast := (J.arrD source "nodes").toList.find? (fun j => J.str? j "name" == some name) |
      throw (IO.userError s!"missing {name}")
    let (_, d) ← checked (function executableReader ast source.compress)
    let C := { base with funs := [(name, d)] }
    let formula ← checked (obligation lowerBodyLoops
      (fun C Γ => Problem.callPre C Γ false [] false [] true) C name false false)
    let observed ← sample C formula
    unless observed == halt do throw (IO.userError s!"{name}: expected {halt}, got {observed}")
    let rows ← checked (Tools.DirectRuntime.check (Json.mkObj [("contract", source), ("function", toJson name)]))
    let rows ← checked rows.getArr?
    unless rows.size == 1 do throw (IO.userError s!"wrong result count {name}")
    let status ← checked (rows[0]!.getObjValAs? String "status")
    if halt == "normal" then
      unless status == "proved" do throw (IO.userError s!"{name}: normal control did not close: {status}")
    else
      unless status != "proved" do throw (IO.userError s!"{name}: abort proved")
    IO.println s!"H90_NARROW {name}: finite={observed}, checker={status}"
  let some param := (J.arrD source "nodes").toList.find? (fun j => J.str? j "name" == some "narrowParam") |
    throw (IO.userError "missing parameter refusal")
  if (function executableReader param source.compress).isOk then
    throw (IO.userError "narrow parameter admitted")
  let some state := (J.nodes packet).find? (fun j => J.str? j "name" == some "NarrowStateRefusal") |
    throw (IO.userError "missing storage refusal")
  if (contract executableReader state).isOk then
    throw (IO.userError "narrow storage admitted")
  IO.println "H90_NARROW parameter/storage refusals retained"
end NarrowLocalRuntimeControls
