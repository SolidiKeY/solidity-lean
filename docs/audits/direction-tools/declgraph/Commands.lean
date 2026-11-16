import Lean

open Lean

namespace Declgraph
abbrev RawEntry := ScopedEnvExtension.Entry Parser.ParserExtension.OLeanEntry
abbrev RichEntry := ScopedEnvExtension.Entry Parser.ParserExtension.Entry
abbrev GrammarState := ScopedEnvExtension.StateStack Parser.ParserExtension.OLeanEntry
  Parser.ParserExtension.Entry Parser.ParserExtension.State

structure GrammarGroup where
  entries : Array RichEntry
  start? : Option (Nat × Nat)
  name : String

structure Grammar where
  env : Environment
  initial : GrammarState
  moduleIndex : NameMap Nat
  chains : Array (Array Nat)
  entries : Array (Array RichEntry)
  groups : Array (Array GrammarGroup)
  cache : IO.Ref (Std.HashMap (Array Nat) GrammarState)

def entryValue : RawEntry → Parser.ParserExtension.OLeanEntry
  | .global e | .scoped _ e => e

def entryDecl? (e : RawEntry) : Option Name :=
  match entryValue e with
  | .parser _ n _ | .category _ n _ => some n
  | _ => none

def appendDistinct (xs ys : Array Nat) : Array Nat := Id.run do
  let mut result := xs
  for y in ys do unless result.contains y do result := result.push y
  return result

unsafe def mkGrammar (env : Environment) (initial : GrammarState) : IO Grammar := do
  let full := Parser.parserExtension.getState env
  let mut indices : NameMap Nat := {}
  for n in [:env.header.moduleNames.size] do indices := indices.insert env.header.moduleNames[n]! n
  let mut allEntries := #[]
  let mut allGroups := #[]
  let mut chains : Array (Array Nat) := #[]
  for i in [:env.header.moduleData.size] do
    let raw := Parser.parserExtension.ext.getModuleEntries env i (level := .private)
    let mut rich : Array RichEntry := #[]
    let mut groups : Array GrammarGroup := #[]
    let mut pending : Array RichEntry := #[]
    for e in raw do
      let parsed ← Parser.parserExtension.descr.ofOLeanEntry full (entryValue e) {env, opts := {}}
      let converted : RichEntry := match e with
        | .global _ => .global parsed
        | .scoped ns _ => .scoped ns parsed
      rich := rich.push converted
      pending := pending.push converted
      if let some name := entryDecl? e then
        let range := declRangeExt.find? (level := .exported) env name <|> declRangeExt.find? (level := .server) env name
        let range := range <|> (← builtinDeclRanges.get).find? name
        let localOwner := env.getModuleIdxFor? name == some i
        let start? := if localOwner then range.map (fun r => (r.range.pos.line - 1, r.range.charUtf16)) else none
        groups := groups.push {entries := pending, start?, name := name.toString}
        pending := #[]
    if !pending.isEmpty then groups := groups.push {entries := pending, start? := none, name := "<unlocated parser metadata>"}
    let mut chain := #[]
    for imp in env.header.moduleData[i]!.imports do
      let some j := indices.find? imp.module | throw (IO.userError s!"missing imported module {imp.module}")
      unless j < i do throw (IO.userError "module data is not topologically ordered")
      chain := appendDistinct chain chains[j]!
    if !rich.isEmpty then chain := chain.push i
    chains := chains.push chain
    allEntries := allEntries.push rich
    allGroups := allGroups.push groups
  let cache ← IO.mkRef {}
  return { env := env, initial := initial, moduleIndex := indices, chains := chains, entries := allEntries, groups := allGroups, cache := cache }

partial def headerImports (header : TSyntax ``Parser.Module.header) : Array Name := Id.run do
  let mut result := #[`Init]
  if let `(Parser.Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imports*) := header then
    if preludeTk?.isSome then result := #[]
    for imp in imports do
      if let `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $name) := imp then
        result := result.push name.getId
  return result

unsafe def contextFor (g : Grammar) (imports : Array Name) : IO (Environment × Array String) := do
  let mut key := #[]
  let mut missing := #[]
  for name in imports do
    match g.moduleIndex.find? name with
    | none => missing := missing.push name.toString
    | some i => key := appendDistinct key g.chains[i]!
  let state ← match (← g.cache.get)[key]? with
    | some state => pure state
    | none => do
      let mut state := g.initial
      for i in key do
        for e in g.entries[i]! do
          state := ScopedEnvExtension.addEntryFn Parser.parserExtension.descr state e
      state := {state with newEntries := []}
      g.cache.modify (·.insert key state)
      pure state
  return (Parser.parserExtension.ext.setState g.env state, missing)

end Declgraph


/- Parse cached-source commands using Lean's own parser. Proof/eval bodies are
   never elaborated. Scope commands and local grammar declarations are replayed;
   macro-generated checks remain outside this explicit-source census.
   Dependencies still come exclusively from native constants and .ilean refs. -/
partial def rawCheckSyntax (stx : Syntax) : Array (String × Syntax) := Id.run do
  let k := stx.getKind
  if stx.isQuot then return #[]
  if k == ``Parser.Command.eval || k == ``Parser.Command.evalBang then return #[("eval", stx)]
  if k == ``Parser.Command.example then return #[("example", stx)]
  let mut result := #[]
  for arg in stx.getArgs do result := result ++ rawCheckSyntax arg
  return result

-- Only these built-in command wrappers preserve execution of their children.
partial def checkSyntax (stx : Syntax) : Array (String × Syntax) := Id.run do
  if stx.isQuot then return #[]
  let k := stx.getKind
  if k == ``Parser.Command.eval || k == ``Parser.Command.evalBang then return #[("eval", stx)]
  if k == ``Parser.Command.example then return #[("example", stx)]
  if k == ``Parser.Command.declaration then
    return stx.getArgs.foldl (fun acc arg => acc ++ checkSyntax arg) #[]
  if k == ``Parser.Command.in then return checkSyntax stx[0] ++ checkSyntax stx[2]
  if k == ``Lean.guardMsgsCmd then
    return checkSyntax stx[stx.getNumArgs - 1]
  return #[]

partial def safeReplayWrappers (stx : Syntax) : Bool :=
  if stx.isOfKind ``Parser.Command.in then
    [``Parser.Command.open, ``Parser.Command.set_option].contains stx[0].getKind &&
      safeReplayWrappers stx[2]
  else true

partial def commandCore (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Command.in then commandCore stx[2] else stx

def scopeSyntax (stx : Syntax) : Bool :=
  [``Parser.Command.namespace, ``Parser.Command.section, ``Parser.Command.end,
   ``Parser.Command.open, ``Parser.Command.set_option, ``Parser.Command.variable,
   ``Parser.Command.include, ``Parser.Command.omit].contains (commandCore stx).getKind

def grammarDirective (cmd : Syntax) : Bool :=
  [``Parser.Command.syntax, ``Parser.Command.notation, ``Parser.Command.mixfix,
   ``Parser.Command.macro, ``Parser.Command.elab, ``Parser.Command.syntaxCat,
   ``Parser.Command.syntaxAbbrev, ``Parser.Command.registerSimpAttr].contains (commandCore cmd).getKind

partial def firstAttrKind? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Parser.Term.attrKind then some stx
  else stx.getArgs.findSome? firstAttrKind?

partial def hasParserAttribute (env : Environment) (stx : Syntax) : Bool := Id.run do
  if stx.isQuot then return false
  if stx.isOfKind ``Parser.Term.attrInstance then
    let attr := stx[1]
    let name := if attr.isOfKind ``Parser.Attr.simple then attr[0].getId.eraseMacroScopes
      else match attr.getKind with | .str _ value => Name.mkSimple value | _ => Name.anonymous
    return match getAttributeImpl env name with
      | .ok impl => impl.descr == "parser" || impl.descr == "Builtin parser"
      | .error _ => false
  return stx.getArgs.any (hasParserAttribute env)

def kindBookkeeping (entry : Declgraph.RichEntry) : Bool :=
  match entry with | .global (.kind _) | .scoped _ (.kind _) => true | _ => false

unsafe def parseSource (grammar : Declgraph.Grammar) (path : String) (module? : Option Name) (probes : Array String := #[]) : IO Json := do
  let input ← IO.FS.readFile path
  let ictx := Parser.InputContext.mk input path
  let (header, initial, headerMessages) ← Parser.parseHeader ictx
  let own? := module?.bind grammar.moduleIndex.find?
  let imports := match own? with
    | some i => grammar.env.header.moduleData[i]!.imports.map (·.module)
    | none => Declgraph.headerImports header
  let (baseEnv, missing) ← Declgraph.contextFor grammar imports
  let mut env := baseEnv.setMainModule (Name.mkSimple s!"DeclgraphParserReplay{hash path}")
  let ownGroups := own?.map (fun i => grammar.groups[i]!) |>.getD #[]
  let bookkeeping := ownGroups.filter (fun g => g.start?.isNone && g.entries.all kindBookkeeping)
  for group in bookkeeping do
    env := Parser.parserExtension.ext.modifyState env fun state => group.entries.foldl (ScopedEnvExtension.addEntryFn Parser.parserExtension.descr) state
  let mut pendingGroups := (ownGroups.filter (fun g => !(g.start?.isNone && g.entries.all kindBookkeeping))).toList
  let mut unlocated : Array String := #[]
  for g in pendingGroups do if g.start?.isNone then unlocated := unlocated.push g.name
  let probeStart := Json.mkObj (probes.toList.map fun t => (t, toJson ((Parser.getTokenTable env).find? t).isSome))
  let mut ps := initial
  let mut cs := Elab.Command.mkState env headerMessages
  let mut roots : Array Json := #[]
  let mut commands := 0
  let mut scopeErrors : Array String := #[]
  let mut unsupported : Array String := #[]
  let mut localRegistrations := 0
  repeat
    let scope := cs.scopes.head!
    let pmctx : Parser.ParserModuleContext := {
      env := cs.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, next, messages) := Parser.parseCommand ictx pmctx ps cs.messages
    ps := next
    cs := { cs with messages }
    if Parser.isTerminalCommand cmd then break
    commands := commands + 1
    if (rawCheckSyntax cmd).size != (checkSyntax cmd).size then
      unsupported := unsupported.push "nested check under unknown command wrapper requires macro expansion"
    for (kind, node) in checkSyntax cmd do
      if let some lo := node.getPos? then
        if let some hi := node.getTailPos? then
          let a := ictx.fileMap.utf8PosToLspPos lo
          let b := ictx.fileMap.utf8PosToLspPos hi
          roots := roots.push <| Json.mkObj [("kind", toJson kind),
            ("range", toJson #[a.line, a.character, b.line, b.character])]
    -- Replay cached syntax registration only after its recorded source command.
    let endPos := ictx.fileMap.utf8PosToLspPos (cmd.getTailPos?.getD ps.pos)
    let startPos := ictx.fileMap.utf8PosToLspPos (cmd.getPos?.getD ps.pos)
    let core := commandCore cmd
    let localGrammar := grammarDirective cmd && (firstAttrKind? core).any Elab.Command.isLocalAttrKind
    let parserAttributeCommand := core.isOfKind ``Parser.Command.attribute && hasParserAttribute cs.env core
    if parserAttributeCommand then unsupported := unsupported.push "separate parser-attribute registration requires a registration trace"
    let registration := grammarDirective cmd || (core.isOfKind ``Parser.Command.declaration && hasParserAttribute cs.env core[0])
    let mut appliedGroups := 0
    let mut remaining := []
    for group in pendingGroups do
      if let some start := group.start? then
        if registration && !localGrammar &&
          (startPos.line < start.1 || (startPos.line == start.1 && startPos.character <= start.2)) &&
          (start.1 < endPos.line || (start.1 == endPos.line && start.2 <= endPos.character)) then
          appliedGroups := appliedGroups + 1
          cs := {cs with env := Parser.parserExtension.ext.modifyState cs.env fun state =>
            group.entries.foldl (ScopedEnvExtension.addEntryFn Parser.parserExtension.descr) state}
        else remaining := remaining ++ [group]
      else remaining := remaining ++ [group]
    pendingGroups := remaining
    if grammarDirective cmd && !localGrammar && appliedGroups == 0 then
      unsupported := unsupported.push "global grammar registration lacks cached registration metadata"
    if (scopeSyntax cmd || localGrammar) && !safeReplayWrappers cmd then
      unsupported := unsupported.push "scope replay rejected a non-whitelisted wrapper prefix"
    if (scopeSyntax cmd || localGrammar) && safeReplayWrappers cmd then
      if localGrammar then localRegistrations := localRegistrations + 1
      let context : Elab.Command.Context := {
        fileName := path, fileMap := ictx.fileMap, cmdPos := cmd.getPos?.getD 0,
        snap? := none, cancelTk? := none }
      let result ← EIO.toIO' <| (Elab.Command.elabCommandTopLevel cmd context).run cs
      match result with
      | .ok (_, state) => cs := state
      | .error ex => scopeErrors := scopeErrors.push (← ex.toMessageData.toString)
  let mut errors : Array String := #[]
  for msg in cs.messages.toList do
    if msg.severity == .error then errors := errors.push (← msg.data.toString)
  let unapplied := pendingGroups.filterMap (fun g => g.start?.map (fun _ => g.name))
  let complete := errors.isEmpty && scopeErrors.isEmpty && missing.isEmpty && unlocated.isEmpty && unsupported.isEmpty && unapplied.isEmpty
  return Json.mkObj [("complete", toJson complete), ("path", toJson path), ("commands", toJson commands),
    ("checks", toJson (if complete then roots else #[])), ("provisional_check_count", toJson roots.size), ("parse_errors", toJson errors), ("scope_errors", toJson scopeErrors),
    ("missing_imports", toJson missing), ("unlocated_parser_groups", toJson unlocated),
    ("unsupported_registrations", toJson unsupported), ("unapplied_parser_groups", toJson unapplied),
    ("local_grammar_replays", toJson localRegistrations), ("bookkeeping_kind_groups", toJson bookkeeping.size),
    ("macro_expansion_checks", toJson "not measured; explicit-source checks only"),
    ("probe_start", probeStart),
    ("probe_end", Json.mkObj (probes.toList.map fun t => (t, toJson ((Parser.getTokenTable cs.env).find? t).isSome)))]

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [modules, paths, output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let names := (← IO.FS.lines modules).filter (· != "")
    let initialGrammar ← ScopedEnvExtension.mkInitial Parser.parserExtension.descr
    let env ← importModules (names.map fun n => { module := n.toName }) {} 0 (loadExts := true)
    let chosen : NameSet := names.foldl (fun acc n => acc.insert n.toName) {}
    let mut compilerEdges : Array (String × String) := #[]
    for (n, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? n then
        if chosen.contains env.header.moduleNames[idx]! then
          if let some impl := Lean.Compiler.getImplementedBy? env n then
            compilerEdges := compilerEdges.push (n.toString, impl.toString)
    IO.FS.writeFile (output ++ ".compiler.json") (toJson compilerEdges).compress
    let grammar ← Declgraph.mkGrammar env initialGrammar
    let out ← IO.FS.Handle.mk output .write
    for row in (← IO.FS.lines paths) do
      if row.startsWith "{" then
        let item ← IO.ofExcept (Json.parse row)
        let path ← IO.ofExcept (item.getObjValAs? String "path")
        let module? := (item.getObjValAs? String "module").toOption.map String.toName
        let probes := (item.getObjValAs? (Array String) "probes").toOption.getD #[]
        out.putStrLn (← parseSource grammar path module? probes).compress
      else
        out.putStrLn (← parseSource grammar row none).compress
    IO.println "COMMAND_INDEX_WRITTEN"
    return 0
  | _ =>
    IO.eprintln "usage: Commands.lean MODULES SOURCE_PATHS OUTPUT"
    return 2
