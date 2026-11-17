/-
Heartbeat recorder for the library ratchet (`ratchet.py` beside this file). A
Lean plugin, compiled on demand and loaded with `lean --plugin`: it leaves the
`.olean` unchanged and writes, for the module being compiled, the heartbeats of
every command to `$HEARTBEATS_DIR/<Module>.tsv`. Counts need `-DElab.async=false`
(one thread; kernel checking counted). Outside the core: imports only Lean.
-/
import Lean
open Lean Elab Command

/-- Heartbeats at the end of the previous command (at first: of the header) and the rows so far. -/
initialize hbState : IO.Ref (Nat × Array String) ← IO.mkRef (0, #[])

/-- Marks the end of the header. Extensions that imported modules register come
after this one, so its first call appends it again to run last; the linter
removes it before the module is written, which keeps it out of the `.olean`. -/
initialize hbExt : PersistentEnvExtension Unit Unit Unit ←
  registerPersistentEnvExtension {
    mkInitial := pure ()
    addImportedFn := fun _ => do
      let first := (← hbState.get).2.isEmpty
      hbState.set (← IO.getNumHeartbeats, #[""])
      if first then
        persistentEnvExtensionsRef.modify fun exts =>
          match exts.find? (·.name == `hbExt) with
          | some ext => exts.push ext
          | none => exts
    addEntryFn := fun _ _ => ()
    exportEntriesFn := fun _ => #[]
  }

def hbLinter : Linter where
  run stx := do
    let now ← IO.getNumHeartbeats
    let (last, rows) ← hbState.get
    let map ← getFileMap
    let line (pos? : Option String.Pos) := pos?.map (map.toPosition · |>.line) |>.getD 0
    let kind := if stx.getKind == ``Parser.Command.declaration then stx[1].getKind else stx.getKind
    let kind := kind.replacePrefix `Lean.Parser.Command .anonymous
    let ns ← getCurrNamespace
    let name := (stx.find? (·.isOfKind ``Parser.Command.declId)).map fun id => s!" {ns ++ id[0].getId}"
    let rows := rows.push s!"{line stx.getPos?}\t{line stx.getTailPos?}\t{now - last}\t{kind}{name.getD ""}"
    hbState.set (now, rows)
    if Parser.isTerminalCommand stx then
      persistentEnvExtensionsRef.modify (·.filter (·.name != `hbExt))
      let some dir ← IO.getEnv "HEARTBEATS_DIR" | return
      -- rows[0] is the header marker: without it the header was not seen
      if rows[0]? != some "" || Elab.async.get (← getOptions) then return
      IO.FS.writeFile (System.FilePath.mk dir / s!"{← getMainModule}.tsv")
        ("\n".intercalate (rows.toList.drop 1) ++ "\n")

initialize addLinter hbLinter
