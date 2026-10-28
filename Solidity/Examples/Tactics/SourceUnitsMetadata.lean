import Solidity.Frontend.SourceUnits

/-! Negative source-unit metadata regressions. A rejected unit contributes no
program or specification; handwritten JSON is not compiler authentication. -/
namespace Solidity.Examples.Tactics.SourceUnitsMetadata
open Lean Elab Command Solidity.Frontend

private def put (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj (((j.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key) ++ [(key, value)])

run_cmd do
  let fixture ← ofExcept (Json.parse (← IO.FS.readFile "tests/solc/source-units/SourceUnits.ast.json"))
  let unit ← ofExcept (Source.readCompilationUnit fixture)
  unless unit.provenance.sources.length == 3 do throwError "lost a source unit"
  let sources ← ofExcept (fixture.getObjValAs? (Array Json) "sourceUnits")
  let header ← ofExcept (fixture.getObjVal? "header")
  let check (label : String) (bad : Json) (reason : String := "") : CommandElabM Unit := do
    match Source.readCompilationUnit bad with
    | .ok _ => throwError "accepted {label}"
    | .error message =>
      unless reason.isEmpty || (message.splitOn reason).length > 1 do
        throwError "{label}: wrong refusal {message}"
  let replace (i : Nat) (value : Json) : Json :=
    put fixture "sourceUnits" (.arr (sources.mapIdx fun k original => if k == i then value else original))
  check "missing dependency" (put fixture "sourceUnits" (.arr (sources.extract 1 sources.size)))
  check "duplicate source name" (replace 1 (put sources[1]! "name" (.str "lib/Math.sol")))
  check "duplicate source identity" (replace 1 (put sources[1]! "id" (toJson (2 : Nat))))
  check "malformed digest" (replace 0 (put sources[0]! "sourceSha256" (.str "0")))
  check "missing main source" (put fixture "header" (put header "mainSource" (.str "missing")))
  check "single-source disguise" (put fixture "header" (put header "provenanceVersion" (toJson (1 : Nat))))
  check "unknown compiler setting" (put fixture "header" (put header "settings"
    (put (← ofExcept (header.getObjVal? "settings")) "unknown" (.bool true))))
  let ast ← ofExcept (sources[0]!.getObjVal? "ast")
  check "foreign location" (replace 0 (put sources[0]! "ast" (put ast "src" (.str "0:1:99"))))
  check "foreign source name" (replace 0 (put sources[0]! "ast" (put ast "absolutePath" (.str "foreign"))))
  check "missing pragmas" (replace 0 (put sources[0]! "acceptedPragmas" (.arr #[])))
  let main ← ofExcept (sources[2]!.getObjVal? "ast")
  let nodes ← ofExcept (main.getObjValAs? (Array Json) "nodes")
  let changed := nodes.map fun node =>
    if (node.getObjValAs? String "nodeType").toOption == some "ImportDirective" then
      put node "sourceUnit" (toJson (999999 : Nat)) else node
  check "foreign import target" (replace 2 (put sources[2]! "ast" (put main "nodes" (.arr changed))))
  for spec in [(.str "invariant false" : Json), .arr #[], .null] do
    check "loop specification metadata" (replace 0 (put sources[0]! "ast" (put ast "loopSpec" spec)))
      "solidity.compilationUnitSpecifications"
  let documented := put ast "documentation" (Json.mkObj [("text", .str "@custom:key invariant false;")])
  check "foreign lexical specification" (replace 0 (put sources[0]! "ast" documented))
    "solidity.compilationUnitSpecifications"
  for path in ["RemapEmpty", "RemapEquals"] do
    let data ← ofExcept (Json.parse (← IO.FS.readFile
      s!"tests/solc/source-units/{path}.ast.json"))
    unless (Source.readCompilationUnit data).isOk do
      throwError "compiler-resolved remapping refused: {path}"

end Solidity.Examples.Tactics.SourceUnitsMetadata
