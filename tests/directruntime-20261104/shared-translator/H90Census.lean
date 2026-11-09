import Solidity.Frontend.Import
import Solidity.Frontend.ExecutableAst.Shared.Compose

/-! Guards H90 canonical-reader parity on CR's exact pinned fixture bytes.
This applies CR's printed-body/name-matching method to the authorized78-file
input set (Q-H90-CENSUS option2), not elaboration or
source/overload adequacy. Per-row compiler identities are retained separately.
Compilation-unit parse refusals are counted and never reported as support. -/
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
#eval show IO Unit from do
  let owned := "tests/directruntime-20261104/shared-translator/artifacts/h90/"
  let inputs ← checked (Json.parse (← IO.FS.readFile (owned ++ "cr-census-inputs.json")))
  let files ← checked (inputs.getObjValAs? (Array Json) "fixtures")
  let mut rows : Array Json := #[]
  let mut parseRefusals : Array Json := #[]
  let mut units := 0
  for entry in files do
    let path ← checked (entry.getObjValAs? String "copy")
    let fixture ← checked (entry.getObjValAs? String "path")
    let packet ← checked (Json.parse (← IO.FS.readFile path))
    let cu ← match Source.readCompilationUnit packet with
      | .ok cu => pure cu
      | .error reason =>
        parseRefusals := parseRefusals.push (Json.mkObj [("fixture", toJson fixture), ("reason", toJson reason)])
        continue
    units := units + 1
    let ast := cu.primary
    for c in (J.nodes ast).filter (fun n => J.kind n == "ContractDefinition") do
      let cname := (J.str? c "name").getD ""
      let existing : List (String × Bool) := match readContract ast cname [] false with
        | .ok sc => sc.funs.map (fun f => (f.sourceName, f.body.toBool))
        | .error _ => []
      for n in (J.arrD c "nodes").toList do
        if J.kind n != "FunctionDefinition" then continue
        let fname := (J.str? n "name").getD ""
        let ex := (existing.find? (·.1 == fname)).map (·.2) |>.getD false
        let canonical := match Shared.function Shared.executableReader n c.compress with
          | .ok _ => "ok" | .error e => e
        rows := rows.push (Json.mkObj [("fixture", toJson fixture), ("contract", toJson cname),
          ("function", toJson fname), ("sourceId", toJson (J.id? n)),
          ("existingPrinted", toJson ex), ("canonical", toJson canonical)])
  let old := rows.filter (fun r => (r.getObjValAs? Bool "existingPrinted").toOption == some true)
  let canonical := rows.filter (fun r => J.str? r "canonical" == some "ok")
  let both := old.filter (fun r => J.str? r "canonical" == some "ok")
  unless files.size == 78 && rows.size == 1655 do
    throw (IO.userError s!"H90 baseline selection changed: {rows.size}/{old.size}")
  let summary := Json.mkObj [("candidateFiles", toJson files.size), ("parsedUnits", toJson units),
    ("functions", toJson rows.size), ("existingPrinted", toJson old.size),
    ("canonicalAdmitted", toJson canonical.size), ("both", toJson both.size)]
  let result := Json.mkObj [("summary", summary), ("parseRefusals", toJson parseRefusals),
    ("rows", toJson rows), ("boundary", toJson "Printed/name-matched census only; not elaboration, source adequacy or overload identity proof.")]
  IO.FS.writeFile (owned ++ "cr-census-results.json") (result.pretty ++ "\n")
  IO.println s!"H90_CENSUS {summary.compress}"
