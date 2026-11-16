import Lean
import Lean.Server.References
open Lean Lean.Elab
namespace DeclgraphRaw

/- Native identifier observations before editor alias coalescing. Source and
   generated syntax stay distinct. These observations are not exhaustive build
   dependencies or executed-program liveness. No string/name-literal guessing.
-/
def nameKey : Name → Json
  | .anonymous => toJson "anonymous"
  | .str parent value => Json.arr #[toJson "str",nameKey parent,toJson value]
  | .num parent value => Json.arr #[toJson "num",nameKey parent,toJson value]

def identJson : Lsp.RefIdent → Json
  | .const moduleName name => Json.mkObj [("kind",toJson "const"),("module_hint",toJson moduleName),("name",toJson name)]
  | .fvar moduleName name => Json.mkObj [("kind",toJson "fvar"),("module_hint",toJson moduleName),("name",toJson name)]

def nativeTarget? : Info → Option Name
  | .ofTermInfo {expr := .const n _, ..} => some n
  | .ofTermInfo {expr := .fvar id, ..} => some id.name
  | .ofFieldInfo info => some info.projName
  | .ofOptionInfo info => some info.declName
  | _ => none

def infoKind : Info → String
  | .ofTermInfo _ => "term" | .ofFieldInfo _ => "field" | .ofOptionInfo _ => "option"
  | _ => "other"

def origin (stx : Syntax) : String :=
  match stx.getHeadInfo with
  | .original .. => "original" | .synthetic .. => "synthetic" | .none => "none"

def rangeJson (r : Lsp.Range) : Json := toJson #[r.start.line,r.start.character,r.end.line,r.end.character]

partial def checkKind? (stx : Syntax) : Option String := do
  if stx.isQuot then none else
  if stx.isOfKind ``Parser.Command.eval || stx.isOfKind ``Parser.Command.evalBang then some "eval" else
  if stx.isOfKind ``Parser.Command.example then some "example" else
  if stx.isOfKind ``Lean.runCmd then some "run_cmd" else
  if stx.isOfKind ``Lean.runElab then some "run_elab" else
  if stx.isOfKind ``Parser.Command.declaration then
    if stx.getArgs.any (·.isOfKind ``Parser.Command.example) then some "example" else none
  else none

structure Capture where
  rows : Array Json := #[]
  aliases : Array InfoTree := #[]
  active : Option String := none
  stack : List (Option String) := []

partial def holes (tree : InfoTree) : Nat :=
  match tree with
  | .hole _ => 1 | .context _ child => holes child
  | .node _ children => children.foldl (fun n child => n + holes child) 0

def collect (trees : Array InfoTree) (fileMap : FileMap) (command : Nat) : Capture :=
  let action : StateM Capture Unit := do
    for tree in trees do
      tree.visitM' (m := StateM Capture) (preNode := fun ctx info _ => do
        let previous := (← get).active
        let nestedCheck :=  match info with | .ofCommandInfo ci => checkKind? ci.stx | _ => none
        modify fun state => {state with stack := previous :: state.stack, active := nestedCheck <|> previous}
        let active := (← get).active
        let common := [("command",toJson command),("check_kind",toJson active),
          ("parent_decl",toJson (ctx.parentDecl?.map Name.toString)),
          ("parent_key",ctx.parentDecl?.map nameKey |>.getD Json.null)]
        if let .ofCommandInfo ci := info then
          let row := Json.mkObj <| common ++ [("record",toJson "command_info"),("syntax_kind",toJson ci.stx.getKind.toString),("origin",toJson (origin ci.stx))]
          modify fun state => {state with rows := state.rows.push row}
        if let some (ident,binder) := Lean.Server.identOf ctx info then
          let row := Json.mkObj <| common ++ [("record",toJson "identifier"),("ident",identJson ident),
            ("name_key",(nativeTarget? info).map nameKey |>.getD Json.null),
            ("is_binder",toJson binder),("info_kind",toJson (infoKind info)),
            ("origin",toJson (origin info.stx)),("range",(info.range?.map fun range => rangeJson (range.toLspRange fileMap)).getD Json.null)]
          modify fun state => {state with rows := state.rows.push row}
        if let .ofFVarAliasInfo alias := info then
          let leaf := InfoTree.context (.commandCtx ctx.toCommandContextInfo) (.node (.ofFVarAliasInfo alias) {})
          modify fun state => {state with aliases := state.aliases.push leaf}
        return true) (postNode := fun _ _ _ => do
          let state ← get
          set {state with active := state.stack.head!, stack := state.stack.tail!})
    return ()
  (action.run {}).2

def syncSetter (stx : Syntax) : Bool :=
  match stx with | `(command| set_option Elab.async false) => true | _ => false

partial def asyncOptionSyntax (stx : Syntax) : Bool :=
  (stx.getKind.toString.endsWith "set_option" && !syncSetter stx &&
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


-- Finished diagnostic-only snapshots occur during synchronous constant
-- realization. Consume their messages; never wait on pending tasks or discard
-- separate info trees/fatal snapshots under a successful observation result.
partial def finishedDiagnostics (tree : Language.SnapshotTree) : BaseIO (Option (MessageLog × Nat)) := do
  if tree.element.infoTree?.isSome || tree.element.isFatal then return none
  let mut messages := tree.element.diagnostics.msgLog
  let mut count := 1
  for child in tree.children do
    if !(← IO.hasFinished child.task) then return none
    let some (nested,n) ← finishedDiagnostics child.task.get | return none
    messages := messages ++ nested
    count := count + n
  return some (messages,count)

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
    let mut originals : Array Lean.Server.Reference := #[]
    let mut originalCommands : Array Nat := #[]
    let mut aliases : Array InfoTree := #[]
    let mut count := 0
    repeat
      let (done,next) ← (checkedCommand.run {inputCtx := ictx}).run state
      state := next
      let some done := done | do
        IO.eprintln "RAW_REFS_UNSUPPORTED explicit async option setter"
        return 2
      let infos := state.commandState.infoState
      if !infos.lazyAssignment.isEmpty ||
          state.commandState.scopes.any (fun scope => Elab.async.get scope.opts) then
        IO.eprintln "RAW_REFS_UNSUPPORTED asynchronous pending work"
        return 2
      let mut snapshotCount := 0
      let mut snapshotMessages : MessageLog := {}
      for task in state.commandState.snapshotTasks do
        if !(← IO.hasFinished task.task) then
          IO.eprintln "RAW_REFS_UNSUPPORTED unfinished snapshot task"
          return 2
        let some (messages,n) ← finishedDiagnostics task.task.get | do
          IO.eprintln "RAW_REFS_UNSUPPORTED non-diagnostic or unfinished snapshot subtree"
          return 2
        snapshotMessages := snapshotMessages ++ messages
        snapshotCount := snapshotCount + n
      state := {state with commandState.messages := state.commandState.messages ++ snapshotMessages}
      let trees := infos.trees.toArray.map (·.substitute infos.assignment)
      let captured := collect trees ictx.fileMap commands
      for row in captured.rows do out.putStrLn row.compress; count := count + 1
      let refs := Lean.Server.findReferences ictx.fileMap trees
      originals := originals ++ refs
      originalCommands := originalCommands ++ refs.map (fun _ => commands)
      aliases := aliases ++ captured.aliases
      out.putStrLn <| (Json.mkObj [("record",toJson "command"),("command",toJson commands),
        ("syntax_kind",toJson state.commands.back!.getKind.toString),("finished_diagnostic_snapshots",toJson snapshotCount),("unresolved_info_holes",toJson (trees.foldl (fun n tree => n + holes tree) 0))]).compress
      state := {state with commands := #[], commandState.infoState := {}, commandState.snapshotTasks := #[]}
      commands := commands + 1
      if done then break
    let combined := Lean.Server.combineIdents aliases originals
    if combined.size != originals.size then throw (IO.userError "native coalescer changed reference cardinality")
    let mut changes := 0
    for i in [:originals.size] do
      let some original := originals[i]? | throw (IO.userError "missing raw reference")
      let some merged := combined[i]? | throw (IO.userError "missing combined reference")
      if original.ident != merged.ident then
        changes := changes + 1
        out.putStrLn <| (Json.mkObj [("record",toJson "coalescing_change"),("command",toJson originalCommands[i]!),
          ("range",rangeJson original.range),("is_binder",toJson original.isBinder),
          ("raw_ident",identJson original.ident),("combined_ident",identJson merged.ident)]).compress
    for msg in state.commandState.messages.toList do IO.println (← msg.toString)
    if state.commandState.messages.hasErrors then return 1
    IO.println s!"RAW_REFS_CAPTURE_PASS {commands} {count} {changes}"
    return 0
  | _ =>
    IO.eprintln "usage: RawRefs.lean SOURCE MODULE OUTPUT"
    return 2
end DeclgraphRaw
unsafe def main := DeclgraphRaw.main
