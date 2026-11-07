import Solidity.Tools.DirectRuntime
import Solidity.Semantics.RunFuel

/-! Source-backed box/diamond pipeline controls. Initial-state finite runs and
trusted executable checker observations are distinct; neither is source preservation,
a Lean proof term or native/WASM closure evidence. -/
namespace SharedTranslatorModalityControls
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def require (p : Bool) (message : String) : IO Unit := do
  unless p do throw (IO.userError message)
private def sample (C : Contract) (formula : Fml C []) (box : Bool) : IO String := do
  match formula with
  | .imp _ (.imp _ (.modal mode program _ _)) =>
    let rightMode := match mode with | .box => box | .diamond => !box
    require rightMode "typed modality differs from source annotation"
    match Prog.runF 4 program (State.init C) with
    | .ok _ => return "normal"
    | .error .panic => return "panic"
    | .error .revert => return "revert"
    | .error e => throw (IO.userError s!"unexpected sample halt {repr e}")
  | _ => throw (IO.userError "unexpected obligation shape")
private def controls : IO Unit := do
  let owned := "tests/directruntime-20261104/shared-translator/"
  let fixture ← checked (Json.parse (← IO.FS.readFile (owned ++ "artifacts/h68-bulk/ModalityControls.ast.json")))
  let ast ← checked (fixture.getObjVal? "ast")
  let some source := (J.nodes ast).find? (fun n => J.kind n == "ContractDefinition")
    | throw (IO.userError "fixture contract missing")
  let base ← checked (contract executableReader source)
  let nodes ← checked (source.getObjValAs? (Array Json) "nodes")
  let mut observations : Array Json := #[]
  for (name, box, halt) in [("normalBox", true, "normal"), ("normalDiamond", false, "normal"),
      ("revertBox", true, "revert"), ("revertDiamond", false, "revert"),
      ("panicBox", true, "panic"), ("panicDiamond", false, "panic")] do
    let some node := nodes.find? (fun n => J.str? n "name" == some name)
      | throw (IO.userError s!"missing {name}")
    let (_, declaration) ← checked (function executableReader node source.compress)
    let C := { base with funs := [(name, declaration)] }
    let formula ← checked (obligation lowerBodyLoops
      (fun C Γ => Problem.callPre C Γ false [] false [] true) C name false box)
    require ((← sample C formula box) == halt) s!"finite sample changed: {name}"
    let results ← checked (Tools.DirectRuntime.check (Json.mkObj [("contract", source),
      ("function", toJson name), ("sourceId", toJson ((J.id? node).getD 0))]))
    let results ← checked results.getArr?
    require (results.size == 1) s!"wrong result count: {name}"
    let result := results[0]!
    let tag := if box then "box" else "diamond"
    require (J.str? result "function" == some name &&
      (result.getObjValAs? Int "sourceId").toOption == J.id? node && J.str? result "tag" == some tag)
      s!"public identity/modality changed: {name}"
    require (J.str? result "verification" == some "direct" && J.str? result "reading" == some "solc")
      s!"result provenance changed: {name}"
    let status ← checked (result.getObjValAs? String "status")
    if halt == "normal" || (box && halt == "revert") then
      require (status == "proved") s!"valid model control did not close: {name}"
    else
      require (["pending", "refuted"].contains status) s!"failing modality control proved: {name}"
    observations := observations.push (Json.mkObj [("finiteHalt", toJson halt), ("checker", result)])
    IO.println s!"modality {name}: {tag}, {halt}, {status}"
  let actual := toJson observations
  let path := owned ++ "modality-observations.json"
  if (← IO.getEnv "SHARED_MODALITY_CAPTURE") == some "1" then
    IO.FS.writeFile path (actual.pretty ++ "\n")
    IO.println "Captured modality observations; frozen checks/review remain required."
  else
    require (actual == (← checked (Json.parse (← IO.FS.readFile path)))) "modality observations changed"
    IO.println "Modality controls: six finite runs and public checker observations matched; no proof/source/native claim."
#eval controls
end SharedTranslatorModalityControls
