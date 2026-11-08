import Lake

/-!
# Read-only metadata dependency content probe

Guards reuse of source-mismatched Dafny metadata artifacts. Uses the installed
Lake content-hash API and Lean import-header parser only: no workspace build,
cache restoration, hash-sidecar write or elaboration of inspected modules is requested.
The Lake hash is not cryptographic; callers separately retain SHA256 evidence.
-/
open Lean Lake System

private def require {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

def main (args : List String) : IO UInt32 := do
  let [input] := args | throw (IO.userError "usage: lake-content-probe INPUT.json")
  let entries ← require <| (← require <| Json.parse (← IO.FS.readFile input)).getArr?
  let mut results : Array Json := #[]
  for entry in entries do
    let file ← require <| entry.getObjValAs? String "path"
    let kind ← require <| entry.getObjValAs? String "kind"
    unless kind == "text" || kind == "binary" do
      throw (IO.userError "unknown content-hash kind")
    let contents ← if kind == "text" then IO.FS.readFile file else pure ""
    let value ← if kind == "text" then pure (Lake.Hash.ofText contents)
      else Lake.computeFileHash (FilePath.mk file) false
    let mut fields := [("path", toJson file), ("kind", toJson kind),
      ("lakeHash", toJson value.toString)]
    if kind == "text" then
      let header ← Lean.parseImports' contents file
      fields := fields ++ [("isModule", toJson header.isModule),
        ("imports", toJson <| header.imports.map fun imp => Json.mkObj
          [("module", toJson imp.module.toString), ("isMeta", toJson imp.isMeta),
           ("importAll", toJson imp.importAll), ("isExported", toJson imp.isExported)])]
    results := results.push (Json.mkObj fields)
  IO.println (toJson results).compress
  return 0
