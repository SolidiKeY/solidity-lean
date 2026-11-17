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

/-- What `lean` would be asked for by Lake (`--lean` mode). -/
structure LeanArgs where
  file : Option String := none
  olean : Option String := none
  ilean : Option String := none
  c : Option String := none
  setup : Option String := none
  json : Bool := false

/-- The subset of `lean`'s command line that Lake's module build uses. `--tstack` is
ignored: the caller sets the main thread's stack. Anything else is refused, so an
artifact is never written under arguments this driver does not honour. -/
def parseLeanArgs : List String → LeanArgs → Except String LeanArgs
  | [], a => pure a
  | "-o" :: f :: rest, a => parseLeanArgs rest { a with olean := some f }
  | "-i" :: f :: rest, a => parseLeanArgs rest { a with ilean := some f }
  | "-c" :: f :: rest, a => parseLeanArgs rest { a with c := some f }
  | "--setup" :: f :: rest, a => parseLeanArgs rest { a with setup := some f }
  | "--json" :: rest, a => parseLeanArgs rest { a with json := true }
  | arg :: rest, a =>
    if arg.startsWith "--tstack=" then parseLeanArgs rest a
    else if arg.startsWith "-" then throw s!"unsupported lean argument {arg}"
    else if a.file.isSome then throw s!"more than one input file ({arg})"
    else parseLeanArgs rest { a with file := some arg }

/-- A path under the working directory, as a relative path (Lake passes absolute ones). -/
def relToCwd (file : String) : IO String := do
  let cwd := (← IO.currentDir).toString ++ "/"
  return if file.startsWith cwd then file.drop cwd.length else file

unsafe def main (args : List String) : IO UInt32 := do
  let (async, args) := match args with
    -- test only (`tests/heartbeats/test_collect.py`): shows what asynchronous
    -- elaboration hides; deadlocks under LEAN_NUM_THREADS=1
    | "--async" :: rest => (true, rest)
    | _ => (false, args)
  -- `--lean REPORT ARGS…`: stand in for `lean ARGS…` as Lake runs it. The JSON object is
  -- appended to REPORT, messages go where `lean` sends them, and the module's
  -- .olean/.ilean/.c are written, so the one elaboration is also Lake's build.
  let (lean?, args) ← match args with
    | "--lean" :: report :: rest => match parseLeanArgs rest {} with
      | .ok a => pure (some (report, a), [])
      | .error e => IO.eprintln s!"hbcollect: {e}"; return 2
    | _ => pure (none, args)
  let (file, modName, setup?) ← match lean?, args with
    | some (_, { file := some file, setup := some setup, .. }), _ =>
      let setup ← ModuleSetup.load setup
      pure (file, setup.name.toString, some setup)
    | none, [file, modName] => pure (file, modName, none)
    | _, _ =>
      IO.eprintln "usage: hbcollect [--async] FILE MODULE | hbcollect --lean REPORT FILE --setup SETUP.json [-o OLEAN] [-i ILEAN] [-c C] [--json]"
      return 2
  if let some setup := setup? then
    unless setup.dynlibs.isEmpty && setup.plugins.isEmpty && !setup.isModule do
      IO.eprintln "hbcollect: --lean does not support dynlibs, plugins or module-system files"
      return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let mainModule := modName.toName
  let opts : Options := ({} : Options)
    |>.set `Elab.async async
    |>.set `internal.cmdlineSnapshots true
  let opts := match setup? with
    | some setup => opts.mergeBy (fun _ _ o => o) setup.options.toOptions
    | none => opts
  let inputCtx := Parser.mkInputContext input file
  let t0 ← IO.monoNanosNow
  let h0 ← IO.getNumHeartbeats
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if lean?.isSome && HeaderSyntax.isModule header then
    IO.eprintln "hbcollect: --lean does not support module-system files"
    return 2
  -- With a setup file the imports come from the artifacts Lake resolved (they may live
  -- only in its cache), as in `lean --setup`; otherwise from the search path.
  let (env, messages) ← processHeaderCore (HeaderSyntax.startPos header)
    ((setup?.bind (·.imports?)).getD (HeaderSyntax.imports header)) (HeaderSyntax.isModule header) opts messages inputCtx
    (mainModule := mainModule) (arts := (setup?.map (·.importArts)).getD {})
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
  let json := lean?.any (·.2.json)
  for m in msgs.toList do
    if json then IO.println (← m.toJson).compress
    else IO.eprint (← m.toString (includeEndPos := false))
  let errors := msgs.toList.filter (·.severity == .error) |>.length
  let total := rows.foldl (· + ·.raw) 0
  let secs (a b : Nat) : String := toString (Float.ofNat (b - a) / 1e9)
  let cmds := rows.toList.map fun r =>
    let name := match r.name with | some n => jsonStr n.toString | none => "null"
    s!"\{\"line\":{r.line},\"kind\":{jsonStr r.kind},\"name\":{name},\"heartbeats\":{units r.raw}}"
  let report := "{" ++ ", ".intercalate [
    s!"\"module\":{jsonStr modName}", s!"\"file\":{jsonStr (← relToCwd file)}",
    s!"\"heartbeats\":{units total}", s!"\"wall_s\":{secs t1 t2}",
    s!"\"import_heartbeats\":{units hImport}", s!"\"import_wall_s\":{secs t0 t1}",
    s!"\"errors\":{errors}", s!"\"commands\":[{",".intercalate cmds}]"] ++ "}"
  match lean? with
  | none => IO.println report
  | some (reportFile, a) =>
    -- As `lean`: no artifact for a module with errors.
    if errors == 0 then
      let env := st.commandState.env
      if let some olean := a.olean then writeModule env olean
      if let some ileanFile := a.ilean then
        -- Info trees are off (they would change the counts), so the .ilean lists the
        -- imports but no references.
        let ilean : Server.Ilean :=
          { module := mainModule, directImports := Server.collectImports header, references := {} }
        IO.FS.writeFile ileanFile <| Json.compress <| toJson ilean
      if let some c := a.c then
        match IR.emitC env mainModule with
        | .ok code => IO.FS.writeFile c code
        | .error e => IO.eprintln s!"hbcollect: {e}"; return 1
    -- Last, so a report exists only when the artifacts do (or the module has errors).
    let h ← IO.FS.Handle.mk reportFile .append
    h.putStrLn report
  return if errors == 0 then 0 else 1
