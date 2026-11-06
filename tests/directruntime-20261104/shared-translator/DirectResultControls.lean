import Solidity.Tools.DirectRuntime

/-! Executable trusted-verifier observations through the canonical public API.
These are not Lean proof terms, Solidity preservation proofs or native/WASM tests.
The separate finite-run controls provide basic positive/negative fixture intent. -/
namespace SharedTranslatorDirectResultControls
open Lean Solidity Solidity.Frontend
private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def require (p : Bool) (message : String) : IO Unit := do
  unless p do throw (IO.userError message)
private def controls : IO Unit := do
  let owned := "tests/directruntime-20261104/shared-translator/"
  let fixture ← checked (Json.parse (← IO.FS.readFile (owned ++ "artifacts/h68-bulk/ComposedReaders.ast.json")))
  let ast ← checked (fixture.getObjVal? "ast")
  let some source := (J.nodes ast).find? (fun n => J.kind n == "ContractDefinition")
    | throw (IO.userError "fixture contract missing")
  let nodes ← checked (source.getObjValAs? (Array Json) "nodes")
  let mut observations : Array Json := #[]
  for (name, intent) in [("memoryAlias", "normal"), ("storageCopy", "normal"),
      ("tupleOrder", "normal"), ("executeFirst", "normal"), ("falseControl", "panic"),
      ("wrongTupleOrder", "panic"), ("discardedFailure", "revert"), ("discardedReadFailure", "revert"),
      ("unsupportedCallTuple", "unsupported"), ("unsupportedReference", "unsupported"),
      ("unsupportedInlineArray", "unsupported"), ("unsupportedDiscardRead", "unsupported")] do
    let some node := nodes.find? (fun n => J.str? n "name" == some name)
      | throw (IO.userError s!"missing {name}")
    let rows ← checked (Tools.DirectRuntime.check (Json.mkObj [("contract", source),
      ("function", toJson name), ("sourceId", toJson ((J.id? node).getD 0))]))
    let rows ← checked rows.getArr?
    require (rows.size == 1) s!"wrong result count: {name}"
    let result := rows[0]!
    let status ← checked (result.getObjValAs? String "status")
    require (J.str? result "function" == some name &&
      (result.getObjValAs? Int "sourceId").toOption == J.id? node) s!"result identity changed: {name}"
    require (J.str? result "verification" == some "direct" && J.str? result "reading" == some "solc")
      s!"result provenance changed: {name}"
    require (J.str? result "tag" == some "diamond") s!"modality changed: {name}"
    if intent == "unsupported" then
      require (status == "unsupported") s!"unsupported shape became decided: {name}"
    else
      require (["proved", "pending", "refuted"].contains status) s!"admitted function changed: {name}"
      if intent == "normal" then
        require (status != "refuted") s!"positive finite control refuted: {name}"
      else
        require (status != "proved") s!"failing diamond control proved: {name}"
    observations := observations.push result
    IO.println s!"direct result {name}: {status}"
  let actual := toJson observations
  let path := owned ++ "direct-result-observations.json"
  if (← IO.getEnv "SHARED_DIRECT_RESULT_CAPTURE") == some "1" then
    IO.FS.writeFile path (actual.pretty ++ "\n")
    IO.println "Captured direct checker observations; frozen gate/review remains required."
  else
    let expected ← checked (Json.parse (← IO.FS.readFile path))
    require (actual == expected) "direct checker observations changed"
    IO.println "Direct result controls: 12 public API observations matched; no proof-term/source/native closure claim."
#eval controls
end SharedTranslatorDirectResultControls
