import Lean.Elab.Frontend
import Lean.Elab.Tactic

/-! Synchronous browser entry point for the project's pinned Lean 4.24 kernel.
Only imported immutable environments are reused; each check gets fresh command
state. The existing Solidity frontend retains its kernel and axiom checks. -/

open Lean

private initialize browserEnvs : IO.Ref (Array (Array Name × Environment)) ← IO.mkRef #[]
private initialize browserCheckSequence : IO.Ref Nat ← IO.mkRef 0

private def browserEnvironment (imports : Array Import) (opts : Options) : IO Environment := do
  let key : Array Name := imports.map (·.module)
  for (oldKey, env) in (← browserEnvs.get) do
    if oldKey == key then return env
  IO.eprintln "Loading the Lean proof environment..."
  initSearchPath "/" ["/workspace"]
  let env ← importModules imports opts 0 (leakEnv := true) (loadExts := true)
  IO.eprintln "Lean proof environment ready."
  browserEnvs.modify (·.push (key, env))
  return env

@[export browser_lean_check]
def browserLeanCheck (source fileName : String) : IO UInt32 := do
  let opts : Options := Elab.async.set {} false
  let inputCtx : Parser.InputContext := Parser.mkInputContext source fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  let imported ← browserEnvironment (Elab.headerToImports header) opts
  let sequence ← browserCheckSequence.modifyGet fun n => (n + 1, n + 1)
  -- Project tactic caches may retain generated alias names between checks.
  -- A fresh main module prevents their names from colliding with this check.
  let env := imported.setMainModule (Name.str `BrowserCheck s!"Check{sequence}")
  let ctx : Elab.Frontend.Context := { inputCtx }
  let state : Elab.Frontend.State := {
    commandState := Elab.Command.mkState env headerMessages opts
    parserState
    cmdPos := parserState.pos
  }
  let (_, finalState) ← StateRefT'.run (ReaderT.run Elab.Frontend.processCommands ctx) state
  IO.eprintln "Lean command checking complete."
  let messages : MessageLog := finalState.commandState.messages
  for message in messages.toList do
    let data : String ← message.data.toString
    let severity : String := match message.severity with
      | .error => "error"
      | .warning => "warning"
      | .information => "information"
    IO.println (Json.mkObj [
      ("fileName", toJson message.fileName),
      ("severity", toJson severity),
      ("message", toJson data),
      ("line", toJson message.pos.line),
      ("column", toJson message.pos.column)
    ]).compress
  return if messages.hasErrors then 1 else 0
