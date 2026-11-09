import Lean
open Lean
open Lean.Elab

/- Re-elaborate one explicitly selected source with exact imported environments.
   Raw saved contexts preserve discarded example/eval declarations.
   Exclusion tests post-command name presence, not final-file CI identity;
   same-name transient versions may be omitted. Imported owners are hints.
   Saved contexts are snapshots, not complete declaration-created/deleted events;
   context IDs describe traversal order rather than creation chronology. Repeated
   contexts are retained deliberately: this is event data, not a liveness census.
   Source commands execute, including #eval; use only authorized check inputs.
   Invoke with Lean -j1, LEAN_NUM_THREADS=1 and a validated warm LEAN_PATH.
-/
def nativeRefs (ci : ConstantInfo) : Array Name := Id.run do
  let mut refs := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then refs := refs ++ value.getUsedConstants
  match ci with
  | .inductInfo v => refs := refs ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => refs := refs.push v.induct
  | .recInfo v =>
    refs := refs ++ v.all.toArray
    for rule in v.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return refs


partial def capture (tree : InfoTree) (postCommandEnv : Environment) (command : Nat)
    (syntaxKind : String) : StateM Nat (Array Json) := do
  match tree with
  | .context (.commandCtx ctx) child =>
    let context ← get
    modify (· + 1)
    let entries := ctx.env.constants.foldStage2 (fun acc name ci =>
      if postCommandEnv.contains name then acc else
      let refs := nativeRefs ci
      let owners := refs.map fun ref => (ctx.env.getModuleIdxFor? ref).map fun i => ctx.env.header.moduleNames[i]!.toString
      acc.push <| Json.mkObj [("command",toJson command),("context",toJson context),
        ("syntax_kind",toJson syntaxKind),("name",toJson name.toString),
        ("refs",toJson (refs.map Name.toString)),("first_import_owner_hints",toJson owners)]) #[]
    return entries ++ (← capture child postCommandEnv command syntaxKind)
  | .context _ child => capture child postCommandEnv command syntaxKind
  | .node _ children =>
    let mut result := #[]
    for child in children do result := result ++ (← capture child postCommandEnv command syntaxKind)
    return result
  | .hole _ => return #[Json.mkObj [("command",toJson command),("unresolved_info_hole",toJson true)]]

-- Conservative syntax preflight prevents known setters from launching async
-- jobs before the pending-task guard can reject them. Macro-created setters
-- remain outside completeness claims; callers should impose a time bound.
partial def asyncOptionSyntax (stx : Syntax) : Bool :=
  (stx.getKind.toString.endsWith "set_option" &&
    stx.getArgs.any (fun arg => arg.isIdent && arg.getId == `Elab.async)) ||
    stx.getArgs.any asyncOptionSyntax

def checkedCommand : Frontend.FrontendM (Option Bool) := do
  Frontend.updateCmdPos
  let cs ← Frontend.getCommandState
  let ictx ← Frontend.getInputContext
  let ps ← Frontend.getParserState
  let scope := cs.scopes.head!
  let pmctx := {env := cs.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls}
  let (cmd,next,messages) := Parser.parseCommand ictx pmctx ps cs.messages
  if asyncOptionSyntax cmd then return none
  modify fun s => {s with commands := s.commands.push cmd}
  Frontend.setParserState next
  Frontend.setMessages messages
  Frontend.elabCommandAtFrontend cmd
  return some (Parser.isTerminalCommand cmd)

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [path,moduleName,output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let input ← IO.FS.readFile path
    let ictx := Parser.mkInputContext input path
    let (header,ps,msgs) ← Parser.parseHeader ictx
    let opts := Elab.async.set {} false
    let (env,msgs) ← processHeader header opts msgs ictx (mainModule := moduleName.toName)
    let mut state : Frontend.State := {commandState := Command.mkState env msgs opts, parserState := ps, cmdPos := ps.pos}
    let out ← IO.FS.Handle.mk output .write
    let mut commands := 0
    let mut contexts := 0
    let mut rows := 0
    repeat
      let (done,next) ← (checkedCommand.run {inputCtx := ictx}).run state
      state := next
      let some done := done | do
        IO.eprintln "CHECK_CONTEXT_CAPTURE_UNSUPPORTED explicit asynchronous option setter"
        return 2
      let infos := state.commandState.infoState
      if !infos.lazyAssignment.isEmpty || !state.commandState.snapshotTasks.isEmpty ||
          state.commandState.scopes.any (fun scope => Elab.async.get scope.opts) then
        IO.eprintln "CHECK_CONTEXT_CAPTURE_UNSUPPORTED pending tasks or enabled asynchronous elaboration"
        return 2
      let syntaxKind := state.commands.back!.getKind.toString
      for tree in infos.trees do
        let (entries,newContexts) := (capture (tree.substitute infos.assignment) state.commandState.env commands syntaxKind).run contexts
        contexts := newContexts
        for entry in entries do
          rows := rows + 1
          out.putStrLn entry.compress
      state := {state with commands := #[], commandState.infoState := {}}
      commands := commands + 1
      if done then break
    for msg in state.commandState.messages.toList do IO.println (← msg.toString)
    if state.commandState.messages.hasErrors then return 1
    IO.println s!"CHECK_CONTEXT_CAPTURE_PASS {commands} {contexts} {rows}"
    return 0
  | _ =>
    IO.eprintln "usage: CheckExport.lean SOURCE MODULE OUTPUT"
    return 2
