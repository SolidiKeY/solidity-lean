import SignatureEnvironment

/-!
Guards regex-only dependency guesses and accidental execution of inventoried
project code. Uses Lean header parsing only: never processes imports, loads
project modules, elaborates bodies, or executes inventoried commands.
Header failures remain records; body/dynamic dependency coverage is unknown.
-/

open Lean

#h62_environment

def parseHeaderRecord (item : Json) : IO Json := do
  let path ← IO.ofExcept (item.getObjValAs? String "path")
  let source ← IO.ofExcept (item.getObjValAs? String "source")
  let (header, state, messages) ← Parser.parseHeader (Parser.mkInputContext source path)
  let failed := messages.hasErrors || state.recovering
  let mut diagnostics : Array Json := #[]
  for message in messages.toList do
    diagnostics := diagnostics.push (toJson (← message.toString))
  let mut imports : Array Json := #[]
  unless failed do
    let all : Array Import := Elab.HeaderSyntax.imports header
    let implicitCount := all.size - (Elab.HeaderSyntax.imports header false).size
    for index in [:all.size] do
      let imp := all[index]!
      imports := imports.push (Json.mkObj [("module", H62Signature.encodeName imp.module),
        ("importAll", toJson imp.importAll), ("isExported", toJson imp.isExported),
        ("isMeta", toJson imp.isMeta), ("implicit", toJson (decide (index < implicitCount)))])
  pure (Json.mkObj [("path", toJson path),
    ("status", toJson (if failed then "header-error" else "parsed-header")),
    ("header_prefix", toJson (source.extract 0 state.pos)),
    ("is_module", if failed then Json.null else toJson (Elab.HeaderSyntax.isModule header)),
    ("imports", Json.arr imports), ("diagnostics", Json.arr diagnostics),
    ("body_parsed", toJson false), ("dynamic_references_known", toJson false)])

def main (args : List String) : IO UInt32 := do
  let [inputPath] := args | throw (IO.userError "expected one JSON input path")
  IO.FS.withFile inputPath .read fun handle => do
    let mut count : Nat := 0
    repeat
      let line ← handle.getLine
      if line.isEmpty then break
      let item ← IO.ofExcept (Json.parse line)
      let record ← parseHeaderRecord item
      IO.println s!"H62_HEADER_RECORD {record.compress}"
      count := count + 1
    let result := Json.mkObj [("format", toJson (1 : Nat)),
      ("lean_version", toJson Lean.versionString), ("records", toJson count)]
    IO.println s!"H62_IMPORT_INVENTORY {result.compress}"
    pure 0
