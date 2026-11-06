import Solidity.Tools.DirectRuntime
import Solidity.Semantics.RunFuel

/-! Canonical reader integration controls. Finite intrinsic execution from
State.init is an external sample, not a Solidity compiler preservation proof.
Listing ready establishes obligation construction only. -/
namespace SharedTranslatorComposedControls
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def require (p : Bool) (message : String) : IO Unit := do
  unless p do throw (IO.userError message)
private def sampleRun (C : Contract) (formula : Fml C []) : IO String := do
  match formula with
  | .imp _ (.imp _ (.modal _ program _ _)) =>
    match Prog.runF 16 program (State.init C) with
    | .ok _ => return "normal"
    | .error .panic => return "panic"
    | .error .revert => return "revert"
    | .error e => throw (IO.userError s!"unexpected intrinsic sample halt {repr e}")
  | _ => throw (IO.userError "unexpected zero-parameter obligation shape")
private def controls : IO Unit := do
  let fixture ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/ComposedReaders.ast.json"))
  let ast ← checked (fixture.getObjVal? "ast")
  let some source := (J.nodes ast).find? (fun n => J.kind n == "ContractDefinition")
    | throw (IO.userError "fixture contract missing")
  let base ← checked (contract executableReader source)
  let nodes ← checked (source.getObjValAs? (Array Json) "nodes")
  for (name, expected) in [("memoryAlias", "normal"), ("storageCopy", "normal"), ("tupleOrder", "normal"),
      ("executeFirst", "normal"), ("falseControl", "panic"), ("wrongTupleOrder", "panic"), ("discardedFailure", "revert"), ("discardedReadFailure", "revert")] do
    let some node := nodes.find? (fun n => J.str? n "name" == some name)
      | throw (IO.userError s!"missing {name}")
    let (_, declaration) ← checked ((function executableReader node source.compress).mapError (fun e => name ++ ": " ++ e))
    let C := { base with funs := [(name, declaration)] }
    let formula ← checked ((obligation lowerBodyLoops
      (fun C Γ => Problem.callPre C Γ false [] false [] true) C name false false).mapError (fun e => name ++ ": " ++ e))
    let observed ← sampleRun C formula
    require (observed == expected) s!"intrinsic sample {name}: expected {expected}, got {observed}"
    let rows ← checked (Tools.DirectRuntime.check (Json.mkObj [("contract", source),
      ("function", toJson name), ("sourceId", toJson ((J.id? node).getD 0)), ("listing", .bool true)]))
    let rows ← checked rows.getArr?
    require (rows.size == 1 && J.str? rows[0]! "status" == some "ready") s!"runtime listing did not use composed reader for {name}"
  for name in ["unsupportedCallTuple", "unsupportedReference", "unsupportedInlineArray", "unsupportedDiscardRead"] do
    let some node := nodes.find? (fun n => J.str? n "name" == some name)
      | throw (IO.userError s!"missing {name}")
    require (match function executableReader node source.compress with | .error _ => true | .ok _ => false)
      s!"unsupported sibling was accepted: {name}"
  IO.println "Composed reader: eight typed intrinsic samples/listings, memory alias/copy/shadowing, tuple order/holes/repeated targets and do-first control checked; four unsupported shapes refused. No source/backend theorem claim."
#eval controls
end SharedTranslatorComposedControls
