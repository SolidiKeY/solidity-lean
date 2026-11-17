/-
Heartbeat collector driver (`scripts/heartbeats/README.md`): elaborates one
module whose imports are already built and prints one JSON object with the
heartbeats of every command. Outside the core: imports only Lean.
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
  let (async, args) := match args with
    -- test only (`tests/heartbeats/test_collect.py`): shows what asynchronous
    -- elaboration hides; deadlocks under LEAN_NUM_THREADS=1
    | "--async" :: rest => (true, rest)
    | _ => (false, args)
  let [file, modName] := args
    | IO.eprintln "usage: hbcollect [--async] FILE MODULE"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let mainModule := modName.toName
  let opts : Options := ({} : Options)
    |>.set `Elab.async async
    |>.set `internal.cmdlineSnapshots true
  let inputCtx := Parser.mkInputContext input file
  let t0 ← IO.monoNanosNow
  let h0 ← IO.getNumHeartbeats
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx (mainModule := mainModule)
  let env := env.setMainModule mainModule
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
    IO.eprint (← m.toString (includeEndPos := false))
  let errors := msgs.toList.filter (·.severity == .error) |>.length
  let total := rows.foldl (· + ·.raw) 0
  let secs (a b : Nat) : String := toString (Float.ofNat (b - a) / 1e9)
  let cmds := rows.toList.map fun r =>
    let name := match r.name with | some n => jsonStr n.toString | none => "null"
    s!"\{\"line\":{r.line},\"kind\":{jsonStr r.kind},\"name\":{name},\"heartbeats\":{units r.raw}}"
  IO.println <| "{" ++ ", ".intercalate [
    s!"\"module\":{jsonStr modName}", s!"\"file\":{jsonStr file}",
    s!"\"heartbeats\":{units total}", s!"\"wall_s\":{secs t1 t2}",
    s!"\"import_heartbeats\":{units hImport}", s!"\"import_wall_s\":{secs t0 t1}",
    s!"\"errors\":{errors}", s!"\"commands\":[{",".intercalate cmds}]"] ++ "}"
  return if errors == 0 then 0 else 1
