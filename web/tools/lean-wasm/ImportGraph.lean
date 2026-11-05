import Lean

/-! Read import headers with the pinned parser; do not elaborate project files.
The static website needs every variant of each transitive import, including IR,
but not unrelated standard-library modules. -/

open Lean

def main (args : List String) : IO Unit := do
  let [standardRoot, projectRoot] := args
    | throw (IO.userError "Expected native Lean source root and project root")
  let frontend ← IO.FS.readFile (System.FilePath.mk projectRoot / "web/browser/BrowserFrontend.lean")
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext frontend "BrowserFrontend.lean")
  if messages.hasErrors then throw (IO.userError "Cannot parse browser frontend imports")
  let mut pending : Array String := #["Solidity.Frontend.Testing"] ++
    (Elab.headerToImports header).map fun i => i.module.toString (escape := false)
  let mut modules : Std.HashMap String (Array String) := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if modules.contains name then continue
    let root := if name == "Solidity" || name.startsWith "Solidity." then projectRoot else standardRoot
    let file := System.FilePath.mk root / (name.replace "." "/" ++ ".lean")
    let source ← IO.FS.readFile file
    let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source file.toString)
    if messages.hasErrors then throw (IO.userError s!"Cannot parse import header: {file}")
    let imports : Array String := (Elab.headerToImports header).map fun i => i.module.toString (escape := false)
    modules := modules.insert name imports
    pending := pending ++ imports
  if modules.contains "Lean" then
    throw (IO.userError "Browser dependencies include the umbrella Lean module; narrow the responsible import")
  let entries : List (String × Json) := modules.toList.map fun (name, imports) => (name, toJson imports)
  IO.println (Json.mkObj [("version", toJson (1 : Nat)), ("modules", Json.mkObj entries)]).compress
