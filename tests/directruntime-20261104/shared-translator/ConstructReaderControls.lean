import Solidity.Frontend.ExecutableAst.Shared.Compose

/-! Source-anchored standalone reader observation controls. They exercise the
actual Shared entrypoints, not a second translator. Kinds without standalone entrypoints are
classified explicitly. No intrinsic/source/backend proof is claimed. -/
namespace SharedTranslatorConstructControls
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value | .error e => throw (IO.userError e)
private def select (j : Json) (pointer : String) : Except String Json := do
  let mut value := j
  for part in (pointer.splitOn "/").drop 1 do
    let key := (part.replace "~1" "/").replace "~0" "~"
    match value with
    | .arr values =>
      let some index := key.toNat? | throw "non-numeric array pointer"
      let some next := values[index]? | throw "array pointer outside fixture"
      value := next
    | _ => value ← value.getObjVal? key
  return value
private def outcome {α : Type} : Except String α → Json
  | .ok _ => Json.mkObj [("status", "decoded")]
  | .error reason => Json.mkObj [("status", "refused"), ("reason", toJson reason)]
/-- Test assembly of the existing two-phase root check, without translating ASTs. -/
private def validated {α : Type} (decoded : Except String α) (node : Json) : Except String α := do
  let result ← decoded
  validateMetadata node
  return result
private def invoke (read : Reader) (route : String) (node : Json) : Json :=
  match route with
  | "expression" => outcome (validated (read.expression node) node)
  | "statements" => outcome (validated (read.statements node) node)
  | "typeName" => outcome (read.typeName node)
  | "function" => outcome (function read node node.compress)
  | "contract" => outcome (contract read node)
  | _ => Json.mkObj [("status", "not-standalone")]
private def producerObservation (route : String) (node : Json) : Json :=
  if route != "expression" then .null else
  match (Solidity.Frontend.expr node).run' {} with
  | .ok text => Json.mkObj [("status", "printed"), ("text", toJson text)]
  | .error (.unsupported text line) => Json.mkObj [("status", "refused"), ("reason", toJson text), ("line", toJson line)]
  | .error (.excluded text line) => Json.mkObj [("status", "excluded"), ("reason", toJson text), ("line", toJson line)]
private def observe (read : Reader) (casesPath : String) (expectedCount : Nat := 57)
    (distinctKinds : Bool := true) : IO Json := do
  let cases ← checked (Json.parse (← IO.FS.readFile casesPath))
  let mut rows : Array Json := #[]
  let mut fixtures : List (String × Json) := []
  for row in ← checked (cases.getObjValAs? (Array Json) "cases") do
    let kind ← checked (row.getObjValAs? String "nodeType")
    let route ← checked (row.getObjValAs? String "route")
    unless ["expression", "statements", "typeName", "function", "contract", "none"].contains route do
      throw (IO.userError "unrecognized standalone route")
    let fixture ← checked (row.getObjValAs? String "fixture")
    let pointer ← checked (row.getObjValAs? String "pointer")
    -- The writer lock keeps fixtures stable throughout this invocation.
    let input ← match fixtures.lookup fixture with
      | some input => pure input
      | none => do
        let input ← checked (Json.parse (← IO.FS.readFile fixture))
        fixtures := (fixture, input) :: fixtures
        pure input
    let node ← checked (select input pointer)
    unless J.kind node == kind do throw (IO.userError "source witness kind changed")
    let natural := invoke read route node
    let negative := if route == "none" then .null else invoke read route (node.setObjVal! "nodeType" "UnknownCompilerNode")
    unless route == "none" || J.str? negative "status" == some "refused" do
      throw (IO.userError s!"unknown {kind} root was accepted by {route}")
    let observed := Json.mkObj [("nodeType", toJson kind), ("route", toJson route),
      ("natural", natural), ("unknownRoot", negative), ("producerExpression", producerObservation route node)]
    let observed := match J.str? row "caseId" with
      | some identity => observed.setObjVal! "caseId" (toJson identity)
      | none => observed
    rows := rows.push observed
  let identities := rows.toList.map (fun row =>
    if distinctKinds then J.kind row else (J.str? row "caseId").getD "")
  unless rows.size == expectedCount && (Std.HashSet.ofList identities).size == expectedCount do
    throw (IO.userError "reader witness coverage changed")
  return toJson rows
/-- H90 reader profiles retain the historical snapshots unchanged. A separate
manifest authenticates every new observation and classifies the narrow-local
admission/refusal refinements; no second translation path is introduced. -/
private def h90Snapshot (legacy : String) : String :=
  "tests/directruntime-20261104/shared-translator/artifacts/h90/reader-profile/" ++
    legacy.replace "/" "__"
private def controls : IO Unit := do
  let owned := "tests/directruntime-20261104/shared-translator/"
  for (variant, read) in [("", reader), ("composed-", executableReader)] do
    for suitePrefix in ["", "fresh-"] do
      let observed ← observe read (owned ++ suitePrefix ++ "construct-reader-cases.json")
      let expectedPath := h90Snapshot (owned ++ variant ++ suitePrefix ++ "construct-reader-matrix.json")
      if (← IO.getEnv "SHARED_H90_READER_CAPTURE") == some "1" ||
        (variant == "composed-" && (← IO.getEnv "SHARED_CONSTRUCT_CAPTURE") == some "1") then
        IO.FS.writeFile expectedPath (observed.pretty ++ "\n")
        IO.println s!"Captured {variant}{suitePrefix}standalone observations; review/frozen comparison still required."
      else
        let expected ← checked (Json.parse (← IO.FS.readFile expectedPath))
        unless observed == expected do throw (IO.userError s!"{variant}{suitePrefix}construct reader observation changed")
        IO.println s!"Construct reader {variant}{suitePrefix}controls: 57 modern kinds, exact standalone outcomes and unknown-root refusals matched; no proof/backend support claim."
private def variantControls : IO Unit := do
  let owned := "tests/directruntime-20261104/shared-translator/"
  for (variant, read) in [("", reader), ("composed-", executableReader)] do
    let observed ← observe read (owned ++ "artifacts/h68-bulk/variant-reader-cases.json") 806 false
    let expectedPath := h90Snapshot (owned ++ "artifacts/h68-bulk/" ++ variant ++ "variant-reader-matrix.json")
    if (← IO.getEnv "SHARED_H90_READER_CAPTURE") == some "1" ||
        (← IO.getEnv "SHARED_VARIANT_CAPTURE") == some "1" then
      IO.FS.writeFile expectedPath (observed.pretty ++ "\n")
      IO.println s!"Captured {variant}806 observed subvariants; review/frozen replay required."
    else
      let expected ← checked (Json.parse (← IO.FS.readFile expectedPath))
      unless observed == expected do throw (IO.userError s!"{variant}variant reader observation changed")
      IO.println s!"Reader {variant}806 observed subvariants: exact outcomes/unknown-root refusals matched; corpus observations only."
private def corpusControls : IO Unit := do
  let owned := "tests/directruntime-20261104/shared-translator/artifacts/corpus-readers/"
  for (name, read) in [("default", reader), ("composed", executableReader)] do
    let observed ← observe read (owned ++ "cases.json") 1926 false
    let expectedPath := h90Snapshot (owned ++ name ++ ".json")
    if (← IO.getEnv "SHARED_H90_READER_CAPTURE") == some "1" ||
        (← IO.getEnv "SHARED_CORPUS_CAPTURE") == some "1" then
      IO.FS.writeFile expectedPath (observed.pretty ++ "\n")
      IO.println s!"Captured {name}1926 structural-form witnesses; frozen replay required."
    else
      let expected ← checked (Json.parse (← IO.FS.readFile expectedPath))
      unless observed == expected do throw (IO.userError s!"{name}corpus reader observation changed")
      IO.println s!"Reader {name}1926 structural forms: exact witness outcomes and callable unknown-root refusals matched; no source/semantic proof."
/-- Explicit opt-in so normal gates retain their existing finite snapshot cost. -/
private def occurrenceControls : IO Unit := do
  unless (← IO.getEnv "SHARED_OCCURRENCE_ENABLE") == some "1" do return
  let owned := "tests/directruntime-20261104/shared-translator/artifacts/occurrence-readers/"
  for (name, read) in [("default", reader), ("composed", executableReader)] do
    let observed ← observe read (owned ++ "cases.json") 55218 false
    let expectedPath := owned ++ name ++ ".json"
    if (← IO.getEnv "SHARED_OCCURRENCE_CAPTURE") == some "1" then
      IO.FS.writeFile expectedPath (observed.pretty ++ "\n")
      IO.println s!"Captured {name}55218 occurrences; frozen replay required."
    else
      let expected ← checked (Json.parse (← IO.FS.readFile expectedPath))
      unless observed == expected do throw (IO.userError s!"{name}occurrence observation changed")
      IO.println s!"Reader {name}all55218 frozen occurrences matched; no semantic/source proof."
#eval controls
#eval variantControls
#eval corpusControls
#eval occurrenceControls
end SharedTranslatorConstructControls
