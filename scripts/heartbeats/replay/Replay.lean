/-
Heartbeat replay driver for `scripts/check-memory-loop-timing.py` (see its
docstring). It does what
`lean --setup SETUP SOURCE -o OLEAN -c C` does, synchronously
(`Elab.async=false`, so kernel checking is counted), and reads
`IO.getNumHeartbeats` around each command as `Tools/Heartbeats/Main.lean`
does. It writes one JSON object in the collector's shape to JSON.
The script compiles it once with `lean -c` and `leanc -rdynamic`; imports only Lean.
-/
import Lean
open Lean Elab Frontend

/-- Raw heartbeats as `maxHeartbeats` units (raw / 1000), exact as a decimal. -/
def units (raw : Nat) : String :=
  let frac := toString (raw % 1000)
  s!"{raw / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- The declared name of a command, if it has a `declId`, under the current namespace. -/
def declName? (ns : Name) (stx : Syntax) : Option Name :=
  (stx.find? (·.isOfKind ``Lean.Parser.Command.declId)).map fun id => ns ++ id[0].getId

def kindOf (stx : Syntax) : String :=
  let k := if stx.getKind == ``Lean.Parser.Command.declaration then stx[1].getKind else stx.getKind
  (k.replacePrefix `Lean.Parser.Command .anonymous).toString

structure Row where
  line : Nat
  kind : String
  name : Option Name
  raw : Nat

def jsonStr (s : String) : String := (Json.str s).compress

unsafe def main (args : List String) : IO UInt32 := do
  let [setupFile, file, olean, cFile, jsonFile] := args
    | IO.eprintln "usage: lean --run Replay.lean SETUP SOURCE OLEAN C JSON"; return 2
  let setup ← ModuleSetup.load setupFile
  setup.dynlibs.forM Lean.loadDynlib
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let mainModule := setup.name
  -- the setup's options override the defaults, as in `lean --setup`; then
  -- synchronous elaboration, so kernel checking runs on this thread and is counted
  let opts : Options := ({} : Options).set `internal.cmdlineSnapshots true
  let opts := opts.mergeBy (fun _ _ hOpt => hOpt) setup.options.toOptions
  let opts := opts.set `Elab.async false
  let inputCtx := Parser.mkInputContext input file
  let t0 ← IO.monoNanosNow
  let h0 ← IO.getNumHeartbeats
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let header : HeaderSyntax := header
  let imports := setup.imports?.getD header.imports
  let (env, messages) ← processHeaderCore header.startPos imports
    (setup.isModule || header.isModule) opts messages inputCtx (trustLevel := 1024)
    (plugins := setup.plugins) (mainModule := mainModule) (arts := setup.importArts)
  let hImport := (← IO.getNumHeartbeats) - h0
  let t1 ← IO.monoNanosNow
  let mut st : Frontend.State :=
    { commandState := { Command.mkState env messages opts with infoState.enabled := false }
      parserState, cmdPos := parserState.pos }
  let mut rows : Array Row := #[]
  repeat
    let hb ← IO.getNumHeartbeats
    let (done, st') ← (processCommand { inputCtx }).run st
    let raw := (← IO.getNumHeartbeats) - hb
    st := st'
    let some stx := st.commands.back? | break
    unless stx.getKind == ``Lean.Parser.Command.eoi do
      let ns := st.commandState.scopes.head!.currNamespace
      let line := (inputCtx.fileMap.toPosition (stx.getPos?.getD st.cmdPos)).line
      rows := rows.push { line, kind := kindOf stx, name := declName? ns stx, raw }
    if done then break
  let t2 ← IO.monoNanosNow
  let msgs := st.commandState.messages
  for m in msgs.toList do
    IO.print (← m.toString (includeEndPos := false))
  let errors := msgs.toList.filter (·.severity == .error) |>.length
  let total := rows.foldl (· + ·.raw) 0
  let secs (a b : Nat) : String := toString (Float.ofNat (b - a) / 1e9)
  let cmds := rows.toList.map fun r =>
    let name := match r.name with | some n => jsonStr n.toString | none => "null"
    s!"\{\"line\":{r.line},\"kind\":{jsonStr r.kind},\"name\":{name},\"heartbeats\":{units r.raw}}"
  IO.FS.writeFile jsonFile <| "{" ++ ", ".intercalate [
    s!"\"module\":{jsonStr mainModule.toString}", s!"\"file\":{jsonStr file}",
    s!"\"heartbeats\":{units total}", s!"\"wall_s\":{secs t1 t2}",
    s!"\"import_heartbeats\":{units hImport}", s!"\"import_wall_s\":{secs t0 t1}",
    s!"\"errors\":{errors}", s!"\"commands\":[{",".intercalate cmds}]"] ++ "}\n"
  if errors != 0 then return 1
  let env := st.commandState.env
  writeModule env olean
  let c ← IO.ofExcept <| IR.emitC env mainModule
  IO.FS.writeFile cFile c
  return 0
