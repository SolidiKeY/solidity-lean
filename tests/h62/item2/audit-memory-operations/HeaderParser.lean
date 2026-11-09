import Lean

/-! Source-signature boundary extractor. This invokes Lean's parser only.
No source declaration is elaborated, evaluated as a theorem, or trusted as a
proof. Imported parser infrastructure is confined to this additive audit tool. -/
open Lean

private def parseHeader (env : Environment) (request : Json) : Except String Json := do
  let source ← request.getObjValAs? String "source"
  let start ← request.getObjValAs? Nat "parse_start_utf8"
  let identity ← request.getObjValAs? Nat "source_id"
  let ictx := Parser.mkInputContext source "<frozen-source>"
  let parser := Parser.andthenFn Parser.whitespace Parser.Command.declSig.fn
  let state := parser.run ictx { env := env, options := {} }
    (Parser.getTokenTable env) { Parser.mkParserState source with pos := ⟨start⟩ }
  if !state.allErrors.isEmpty then
    return Json.mkObj [("source_id", toJson identity), ("status", toJson "parse-error"),
      ("error", toJson (state.toErrorMsg ictx))]
  let signature := state.stxStack.back
  match signature.getTailPos? with
  | none => throw "No source end position for declaration signature"
  | some tail =>
    return Json.mkObj [("source_id", toJson identity), ("status", toJson "source-parsed"),
      ("syntax_kind", toJson signature.getKind.toString),
      ("header_end_utf8", toJson tail.byteIdx)]

/- The compiler has already loaded the standard syntax extensions here.
Only the helper's own definitions elaborate; frozen source is parser input. -/
run_elab do
  let some inputPath ← IO.getEnv "H62_HEADER_INPUT"
    | throwError "H62_HEADER_INPUT is required"
  let some outputPath ← IO.getEnv "H62_HEADER_OUTPUT"
    | throwError "H62_HEADER_OUTPUT is required"
  let env ← Lean.getEnv
  let inputText ← IO.FS.readFile inputPath
  let input ← IO.ofExcept (Json.parse inputText)
  let requests ← IO.ofExcept (input.getObjValAs? (Array Json) "requests")
  let mut results : Array Json := #[]
  for request in requests do
    results := results.push (← IO.ofExcept (parseHeader env request))
  let output := Json.mkObj [("boundary",toJson "source parser only; no kernel signatures or proofs"),
    ("results",Json.arr results)]
  IO.FS.writeFile outputPath (output.pretty ++ "\n")
