import Lean
open Lean Lean.Elab
namespace DeclgraphCompactRoots
/- Saved native environments, never the final file environment. Parent-decl
   metadata under actual check commands selects candidate temporary roots.
   Missing roots/constant versions remain explicit; snapshot repetitions are not
   distinct successful checks. Pointer origin matches are positive evidence only.
-/
def nameKey : Name → Json
  | .anonymous => toJson "anonymous"
  | .str parent value => Json.arr #[toJson "str",nameKey parent,toJson value]
  | .num parent value => Json.arr #[toJson "num",nameKey parent,toJson value]

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

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

partial def checkKind? (stx : Syntax) : Option String := do
  if stx.isQuot then none else
  if stx.isOfKind ``Parser.Command.eval || stx.isOfKind ``Parser.Command.evalBang then some "eval" else
  if stx.isOfKind ``Parser.Command.example then some "example" else
  if stx.isOfKind ``Lean.runCmd then some "run_cmd" else
  if stx.isOfKind ``Lean.runElab then some "run_elab" else
  if stx.isOfKind ``Parser.Command.declaration then
    if stx.getArgs.any (·.isOfKind ``Parser.Command.example) then some "example" else none
  else none


def rangeJson (r : DeclarationRange) : Json :=
  toJson #[r.pos.line - 1,r.charUtf16,r.endPos.line - 1,r.endCharUtf16]

structure Snapshot where
  env : Environment
  seeds : NameSet := {}

structure Capture where
  snapshots : Array Snapshot := #[]
  roots : Array Json := #[]
  checks : Array Json := #[]
  missingParents : Array Json := #[]
  noParent : Nat := 0
  holes : Nat := 0
  noContext : Nat := 0

partial def collectTree (tree : InfoTree) (ctx? : Option ContextInfo)
    (snapshot? : Option Nat) (active : Option String) (command : Nat) : StateM Capture Unit := do
  match tree with
  | .hole _ => modify fun s => {s with holes := s.holes + 1}
  | .context inner child =>
    let merged := inner.mergeIntoOuter? ctx?
    match inner, merged with
    | .commandCtx _, some ctx =>
      let id := (← get).snapshots.size
      modify fun s => {s with snapshots := s.snapshots.push {env := ctx.env}}
      collectTree child merged (some id) active command
    | _, _ => collectTree child merged snapshot? active command
  | .node info children =>
    let nested := match info with | .ofCommandInfo ci => checkKind? ci.stx | _ => none
    if let some kind := nested then
      modify fun s => {s with checks := s.checks.push <| Json.mkObj [("record",toJson "check_event"),("command",toJson command),("check_kind",toJson kind)]}
    let active := nested <|> active
    if let some kind := active then
      match ctx?, snapshot? with
      | some ctx, some id =>
        if let some parent := ctx.parentDecl? then
          if let some ci := ctx.env.find? parent then
            modify fun s => {s with
              snapshots := s.snapshots.modify id fun snap => {snap with seeds := snap.seeds.insert parent}
              roots := s.roots.push <| Json.mkObj [("record",toJson "root_event"),("command",toJson command),
                ("snapshot",toJson id),("check_kind",toJson kind),("name",toJson ci.name.toString),
                ("name_key",nameKey ci.name),("constant_kind",toJson (constantKind ci))]}
          else
            modify fun s => {s with missingParents := s.missingParents.push <| Json.mkObj [("record",toJson "missing_parent"),("command",toJson command),("snapshot",toJson id),("name_key",nameKey parent)]}
        else modify fun s => {s with noParent := s.noParent + 1}
      | _, _ =>
        if (match info with | .ofTermInfo _ | .ofTacticInfo _ => true | _ => false) then
          modify fun s => {s with noContext := s.noContext + 1}
    let next := info.updateContext? ctx?
    for child in children do collectTree child next snapshot? active command

/- Exact positive payload-pointer memoization. Holding every CI payload in the
   pool prevents address reuse. Different payloads are never merged, even if
   names or printed expressions happen to agree. Per-snapshot provenance/ranges
   stay on binding references, outside the immutable definition pool. -/
structure Entry where
  info : ConstantInfo
  refs : Array Name
  emitted : Bool := false

structure Pool where
  entries : Array Entry := #[]
  byName : NameMap (Array Nat) := {}

unsafe def samePayload (a b : ConstantInfo) : Bool :=
  match a,b with
  | .axiomInfo x,.axiomInfo y => ptrEq x y
  | .defnInfo x,.defnInfo y => ptrEq x y
  | .thmInfo x,.thmInfo y => ptrEq x y
  | .opaqueInfo x,.opaqueInfo y => ptrEq x y
  | .quotInfo x,.quotInfo y => ptrEq x y
  | .inductInfo x,.inductInfo y => ptrEq x y
  | .ctorInfo x,.ctorInfo y => ptrEq x y
  | .recInfo x,.recInfo y => ptrEq x y
  | _,_ => false

unsafe def intern (pool : Pool) (ci : ConstantInfo) : IO (Nat × Pool) := do
  let prior := (pool.byName.find? ci.name).getD #[]
  for id in prior do
    let some entry := pool.entries[id]? | throw (IO.userError "Invalid definition pool index")
    if samePayload entry.info ci then return (id,pool)
  let id := pool.entries.size
  let entry : Entry := { info := ci, refs := nativeRefs ci }
  let next : Pool := { entries := pool.entries.push entry, byName := pool.byName.insert ci.name (prior.push id) }
  return (id,next)

unsafe def exportSnapshot (out : IO.FS.Handle) (snapshot : Snapshot) (id command : Nat)
    (sourceModule : String) (selected : NameSet)
    (origins : NameMap (Array (Name × ConstantInfo))) (initialPool : Pool) : IO (Nat × Pool) := do
  let mut pending := snapshot.seeds.toArray
  let mut seen : NameSet := {}
  let mut missing : Array Json := #[]
  let mut unresolvedOrigins := 0
  let mut emitted := 0
  let mut pool := initialPool
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := snapshot.env.find? n | do
      missing := missing.push (nameKey n)
      continue
    unless n == ci.name do throw (IO.userError "Environment key/CI name mismatch")
    let (ciId,nextPool) ← intern pool ci
    pool := nextPool
    let some entry := pool.entries[ciId]? | throw (IO.userError "Missing interned definition")
    pending := pending ++ entry.refs
    let pointerCandidates := ((origins.find? n).getD #[]).filter fun pair => ptrEq pair.2 ci
    let isLocal := snapshot.env.constants.map₂.contains n
    let modules := pointerCandidates.map (·.1)
    let ownRange := if isLocal then (declRangeExt.getState snapshot.env).find? n else none
    if !isLocal && modules.isEmpty then unresolvedOrigins := unresolvedOrigins + 1
    if isLocal || modules.any selected.contains then
      if !entry.emitted then
        out.putStrLn <| (Json.mkObj [("record",toJson "definition"),("id",toJson ciId),
          ("name",toJson n.toString),("name_key",nameKey n),("constant_kind",toJson (constantKind ci)),
          ("refs",Json.arr (entry.refs.map fun ref => Json.mkObj [("name",toJson ref.toString),("name_key",nameKey ref)]))]).compress
        pool := {pool with entries := pool.entries.modify ciId fun entry => {entry with emitted := true}}
      emitted := emitted + 1
      out.putStrLn <| (Json.mkObj [("record",toJson "binding_ref"),("definition",toJson ciId),
        ("command",toJson command),("snapshot",toJson id),("in_stage2",toJson isLocal),
        ("elaborating_module",if isLocal then toJson sourceModule else Json.null),
        ("imported_pointer_modules",toJson (modules.map Name.toString)),
        ("is_root",toJson (snapshot.seeds.contains n)),
        ("own_range",ownRange.map (fun r => rangeJson r.range) |>.getD Json.null)]).compress
  out.putStrLn <| (Json.mkObj [("record",toJson "snapshot_summary"),("command",toJson command),("snapshot",toJson id),
    ("root_names",Json.arr (snapshot.seeds.toArray.map nameKey)),("visited_names",toJson seen.size),
    ("emitted_bindings",toJson emitted),("missing_names",toJson missing),("unresolved_import_origins",toJson unresolvedOrigins)]).compress
  return (emitted,pool)

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
  | [path,moduleName,modules,output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let selected := (← IO.FS.lines modules).foldl (fun set name => if name.isEmpty then set else set.insert name.toName) ({} : NameSet)
    if selected.isEmpty then throw (IO.userError "Empty selected module manifest")
    let input ← IO.FS.readFile path
    let ictx := Parser.mkInputContext input path
    let (header,ps,msgs) ← Parser.parseHeader ictx
    let opts := Elab.async.set {} false
    let (env,msgs) ← processHeader header opts msgs ictx (mainModule := moduleName.toName)
    let mut origins : NameMap (Array (Name × ConstantInfo)) := {}
    for i in [:env.header.moduleData.size] do
      for ci in env.header.moduleData[i]!.constants do
        origins := origins.insert ci.name (((origins.find? ci.name).getD #[]).push (env.header.moduleNames[i]!,ci))
    let mut state : Frontend.State := {commandState := Command.mkState env msgs opts, parserState := ps, cmdPos := ps.pos}
    let out ← IO.FS.Handle.mk output .write
    let mut commands := 0
    let mut checks := 0
    let mut roots := 0
    let mut snapshots := 0
    let mut bindings := 0
    let mut pool : Pool := {}
    repeat
      let (done,next) ← (checkedCommand.run {inputCtx := ictx}).run state
      state := next
      let some done := done | do
        IO.eprintln "SNAPSHOT_ROOTS_UNSUPPORTED explicit async setter"
        return 2
      let infos := state.commandState.infoState
      if !infos.lazyAssignment.isEmpty || state.commandState.scopes.any (fun scope => Elab.async.get scope.opts) then
        IO.eprintln "SNAPSHOT_ROOTS_UNSUPPORTED asynchronous pending work"
        return 2
      let mut messages : MessageLog := {}
      let mut diagnostics := 0
      for task in state.commandState.snapshotTasks do
        if !(← IO.hasFinished task.task) then
          IO.eprintln "SNAPSHOT_ROOTS_UNSUPPORTED unfinished task"
          return 2
        let some (log,n) ← finishedDiagnostics task.task.get | do
          IO.eprintln "SNAPSHOT_ROOTS_UNSUPPORTED non-diagnostic snapshot"
          return 2
        messages := messages ++ log
        diagnostics := diagnostics + n
      state := {state with commandState.messages := state.commandState.messages ++ messages}
      let mut captured : Capture := {}
      for tree in infos.trees do
        captured := ((collectTree (tree.substitute infos.assignment) none none none commands).run captured).2
      if captured.holes != 0 || captured.noContext != 0 then
        IO.eprintln "SNAPSHOT_ROOTS_UNSUPPORTED incomplete info context"
        return 2
      for check in captured.checks do out.putStrLn check.compress
      checks := checks + captured.checks.size
      for missing in captured.missingParents do out.putStrLn missing.compress
      for root in captured.roots do out.putStrLn root.compress
      roots := roots + captured.roots.size
      for i in [:captured.snapshots.size] do
        let some snapshot := captured.snapshots[i]? | throw (IO.userError "Missing native snapshot")
        if !snapshot.seeds.isEmpty then
          snapshots := snapshots + 1
          let (n,nextPool) ← exportSnapshot out snapshot i commands moduleName selected origins pool
          bindings := bindings + n
          pool := nextPool
      out.putStrLn <| (Json.mkObj [("record",toJson "command"),("command",toJson commands),
        ("finished_diagnostic_snapshots",toJson diagnostics),("active_nodes_without_parent",toJson captured.noParent),("missing_parent_events",toJson captured.missingParents.size)]).compress
      state := {state with commands := #[],commandState.infoState := {},commandState.snapshotTasks := #[]}
      commands := commands + 1
      if done then break
    for msg in state.commandState.messages.toList do IO.println (← msg.toString)
    if state.commandState.messages.hasErrors then return 1
    let definitions := pool.entries.foldl (fun count entry => count + if entry.emitted then 1 else 0) 0
    IO.println s!"COMPACT_ROOTS_PASS {commands} {checks} {roots} {snapshots} {bindings} {definitions}"
    return 0
  | _ => IO.eprintln "usage: CompactRoots.lean SOURCE MODULE SELECTED-MODULES OUTPUT"; return 2
end DeclgraphCompactRoots
unsafe def main := DeclgraphCompactRoots.main
