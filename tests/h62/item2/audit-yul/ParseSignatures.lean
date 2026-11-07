import Lean
/-! Read-only parser companion. It extracts original syntax spans, never
elaborates a theorem or claims a premise witness. Errors remain evidence. -/
open Lean Parser
partial def collect (stx : Syntax) : Array Json := Id.run do
  let mut rows := #[]
  if stx.getKind == ``Command.theorem || stx.getKind == ``Command.example then
    for child in stx.getArgs do
      if child.getKind == ``Command.declSig || child.getKind == ``Command.optDeclSig then
        if let some p := stx.getPos? then
          if let some q := child.getTailPos? then
            rows := rows.push <| Json.mkObj [
              ("start_byte", toJson p.byteIdx), ("end_byte", toJson q.byteIdx),
              ("kind", toJson stx.getKind.toString),
              ("signature_missing", toJson child.hasMissing)]
  for child in stx.getArgs do
    rows := rows ++ collect child
  return rows

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Lean }] {} 0 (loadExts := true)
  let files ← match args with
    | ["--files", path] => do
      let text ← IO.FS.readFile path
      pure ((text.splitOn "\n").filter (· != ""))
    | _ => pure args
  for file in files do
    let text ← IO.FS.readFile file
    let ctx := mkInputContext text file
    let (_, initial, initialMessages) ← parseHeader ctx
    let mut state := initial
    let mut messages := initialMessages
    let mut rows := #[]
    repeat
      let (stx, next, msgs) := parseCommand ctx { env := env, options := {} } state messages
      rows := rows ++ collect stx
      if isTerminalCommand stx then break
      if next.pos == state.pos then break
      state := next
      messages := msgs
    let mut diagnostics : Array String := #[]
    for msg in messages.toList do
      diagnostics := diagnostics.push (← msg.toString)
    IO.println <| (Json.mkObj [("file", toJson file), ("source_text", toJson text), ("signatures", toJson rows),
      ("diagnostics", toJson diagnostics), ("parse_errors", toJson messages.hasErrors)]).compress
