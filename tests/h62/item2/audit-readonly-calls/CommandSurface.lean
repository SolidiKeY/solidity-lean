import Lean

/-! Guard mutual-block ends and equation bodies being mistaken for theorem headers.
SDK-only syntax parsing: inventoried imports and commands are never elaborated or
executed. Parser ranges are surface evidence, not kernel types, source adequacy,
complete custom-syntax coverage or live ownership. Errors retain all diagnostics.
-/
open Lean
namespace Solidity.H62.CommandSurface

def span (s : Syntax) : Json :=
  match s.getPos?, s.getTailPos? with
  | some start, some stop => Json.mkObj [("start",toJson start.byteIdx),("end",toJson stop.byteIdx)]
  | _, _ => Json.null

partial def ids (s : Syntax) : Array String :=
  if s.isIdent then #[s.getId.toString]
  else s.getArgs.foldl (fun acc x => acc ++ ids x) #[]

partial def records (s : Syntax) : Array Json := Id.run do
  if s.isOfKind ``Parser.Command.mutual then
    let mut out := #[Json.mkObj [("kind",toJson "mutual-enter"),("range",span s)]]
    for child in s[1].getArgs do out := out ++ records child
    return out.push (Json.mkObj [("kind",toJson "mutual-exit"),("range",span s)])
  let kind := s.getKind.toString
  let mut fields := [("kind",toJson kind),("range",span s)]
  if s.isOfKind ``Parser.Command.declaration then
    let item := s[1]
    fields := fields ++ [("declaration_kind",toJson item.getKind.toString)]
    if item.isOfKind ``Parser.Command.theorem then
      fields := fields ++ [("name",toJson item[1][0].getId.toString),
        ("name_range",span item[1]),("signature_range",span item[2]),
        ("keyword_range",span item[0]),("body_kind",toJson item[3].getKind.toString),
        ("modifiers_range",span s[0])]
  else if s.isOfKind ``Parser.Command.namespace || s.isOfKind ``Parser.Command.section || s.isOfKind ``Parser.Command.end then
    fields := fields ++ [("identifiers",toJson (ids s))]
  return #[Json.mkObj fields]

def parseRecord (env : Environment) (item : Json) : IO Json := do
  let path ← IO.ofExcept (item.getObjValAs? String "path")
  let source ← IO.ofExcept (item.getObjValAs? String "source")
  let ctx := Parser.mkInputContext source path
  let (_, initial, headerMessages) ← Parser.parseHeader ctx
  let mut state := initial
  let mut messages := headerMessages
  let mut rows := #[]
  let mut count := 0
  let mut terminal := ""
  repeat
    let old := state.pos
    let (command, next, log) := Parser.parseCommand ctx { env := env, options := {} } state messages
    state := next; messages := log
    if Parser.isTerminalCommand command then
      terminal := command.getKind.toString
      break
    if state.pos <= old then throw (IO.userError "parser made no progress")
    rows := rows ++ records command
    count := count + 1
  let mut diagnostics := #[]
  for msg in messages.toList do diagnostics := diagnostics.push (toJson (← msg.toString))
  return Json.mkObj [("path",toJson path),("status",toJson (if messages.hasErrors || state.recovering then "parser-error" else if terminal != "Lean.Parser.Command.eoi" then "terminal-before-eof" else "parsed-standard-syntax")),
    ("terminal",toJson terminal),("parsed_position",toJson state.pos.byteIdx),("commands",toJson count),("records",Json.arr rows),("diagnostics",Json.arr diagnostics),
    ("project_imports_loaded",toJson false),("commands_elaborated",toJson false),("kernel_binding",toJson false)]
end Solidity.H62.CommandSurface

open Lean Elab Command in
elab "#audit_command_surface " path:str : command => do
  let env ← getEnv
  let content ← IO.FS.readFile path.getString
  for line in content.splitOn "\n" do
    if line.isEmpty then continue
    let item ← IO.ofExcept (Json.parse line)
    let record ← Solidity.H62.CommandSurface.parseRecord env item
    logInfo m!"H62_COMMAND_SURFACE {record.compress}"
