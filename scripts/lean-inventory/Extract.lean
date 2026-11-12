import Lean
import Solidity.Tools.Goal

/-! Read-only declaration-graph extractor for `inventory.py` (plan step
k1-lean-inventory). Adapted from `docs/audits/direction-tools/declgraph/ModuleExport.lean`
(kernel constants, `declRangeExt` ranges), which stays unchanged.

It runs only when `LEAN_INVENTORY_OUT` is set, so an ordinary per-file check of this
file loads nothing. `LEAN_INVENTORY_MODULES` names a file of `group<TAB>module` lines:
each group's modules are imported together from the built `.olean` files (never
elaborated from source) and dumped as JSON lines. Groups keep executables whose roots
each define `main` apart.

Per project constant (modules outside `Init`, `Lean`, `Std`, `Lake`) it records the
constants its type and value use (kernel `getUsedConstants`; inductive, constructor and
recursor links), its declaration range, whether it is an instance or a default simp
lemma, whether its type mentions the `Lean` namespace (a metaprogram candidate), its
`implemented_by` target, and, for metaprogram candidates, the project constants named by
`Name` literals in its value (quotation identifiers). Elaborator-time uses (tactics,
macros, elaborators run while checking) do not appear in kernel terms; `inventory.py`
represents them as gaps. -/

open Lean Meta

namespace Solidity.LeanInventory.Extract

def coreRoots : List Name := [`Init, `Lean, `Std, `Lake]

def isCore (m : Name) : Bool := coreRoots.contains m.getRoot

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def kernelRefs (ci : ConstantInfo) : Array Name := Id.run do
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

/-- The `Name` an expression builds from literals, if it is one. -/
partial def nameLit? (e : Expr) : Option Name :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  let str? (a : Expr) : Option String := match a with
    | .lit (.strVal s) => some s
    | _ => none
  match fn with
  | .const ``Name.anonymous _ => some .anonymous
  | .const ``Name.mkStr _ =>
    if h : args.size = 2 then do
      let p ← nameLit? args[0]
      let s ← str? args[1]
      pure (.str p s)
    else none
  | .const c _ =>
    if c.getPrefix == ``Name && (c.toString.startsWith "Lean.Name.mkStr") then
      args.foldlM (init := Name.anonymous) fun acc a => do pure (.str acc (← str? a))
    else none
  | _ => none

def nameLits (e : Expr) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let mut stack : Array Expr := #[e]
  let mut seen : Std.HashSet Expr := {}
  while h : stack.size > 0 do
    let x := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    if let some n := nameLit? x then
      if !n.isAnonymous then out := out.push n
      continue
    match x with
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
    | .letE _ t v b _ => stack := stack.push t |>.push v |>.push b
    | .mdata _ b => stack := stack.push b
    | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return out

/-- Order-preserving deduplication in linear time (`List.eraseDups` is quadratic). -/
def dedup (xs : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for x in xs do
    if !seen.contains x then
      seen := seen.insert x
      out := out.push x
  return out

def mentionsLean (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => c.getRoot == `Lean

def rangeJson (r : DeclarationRange) : Json :=
  toJson #[r.pos.line, r.endPos.line]

/-- Elaborates an executable root's source (it is not importable: no `lean_lib` builds an
`.olean` for it) over the built `.olean` files of its imports. -/
def elabRoot (file : System.FilePath) (mainModule : Name) : IO Environment := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx (mainModule := mainModule)
  let s ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages {})
  if s.commandState.messages.hasErrors then
    throw <| IO.userError s!"{file}: elaboration reported errors"
  return s.commandState.env

/-- One module's constants as JSON lines. -/
def dumpConsts (out : IO.FS.Stream) (env : Environment) (group : String) (m : Name)
    (isProject : Name → Bool) (ranges : Name → Option DeclarationRanges)
    (constants : Array ConstantInfo) : IO Unit := do
  let simps := simpExtension.getState env
  let insts := (instanceExtension.getState env).instanceNames
  for ci in constants do
    let n := ci.name
    let refs := dedup ((kernelRefs ci).filter isProject)
    let isMeta := mentionsLean ci.type
    let lits : Array Name := if isMeta then
        match ci.value? (allowOpaque := true) with
        | some v => (nameLits v).filter fun l => l != n && isProject l
        | none => #[]
      else #[]
    let impl := (Compiler.implementedByAttr.getParam? env n).map (·.toString)
    let mut fields : List (String × Json) :=
      [("r", "const"), ("g", toJson group), ("m", toJson m.toString),
       ("n", toJson n.toString), ("k", toJson (constantKind ci)),
       ("refs", toJson (refs.map Name.toString))]
    if let some r := ranges n then fields := fields ++ [("range", rangeJson r.range)]
    if insts.contains n then fields := fields ++ [("inst", toJson true)]
    if simps.isLemma (.decl n) then fields := fields ++ [("simp", toJson true)]
    if isMeta then fields := fields ++ [("meta", toJson true)]
    if !lits.isEmpty then
      fields := fields ++ [("lits", toJson ((dedup lits).map Name.toString))]
    if let some t := impl then fields := fields ++ [("impl", toJson t)]
    out.putStrLn (Json.mkObj fields).compress

/-- Dumps the project modules of `env`, and with `root? = some (m, _)` the constants the
elaborated root module `m` added. -/
def dumpEnv (out : IO.FS.Stream) (group : String) (env : Environment)
    (root? : Option Name := none) : IO Unit := do
  let isProject (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => !isCore env.header.moduleNames[i]!
    | none => root?.isSome && env.constants.map₂.contains n
  for i in [:env.header.moduleData.size] do
    let m := env.header.moduleNames[i]!
    if isCore m then continue
    let data := env.header.moduleData[i]!
    out.putStrLn <| (Json.mkObj [("r", "module"), ("g", toJson group), ("m", toJson m.toString),
      ("imports", toJson (data.imports.map (·.module.toString)))]).compress
    let mut ranges : NameMap DeclarationRanges := {}
    for (n, r) in declRangeExt.getModuleEntries env i (level := .private) do
      ranges := ranges.insert n r
    dumpConsts out env group m isProject ranges.find? data.constants
  if let some m := root? then
    let localConsts := env.constants.map₂.toList.map (·.2) |>.toArray.qsort (·.name.lt ·.name)
    out.putStrLn <| (Json.mkObj [("r", "module"), ("g", toJson group), ("m", toJson m.toString),
      ("imports", toJson (env.header.imports.map (·.module.toString)))]).compress
    dumpConsts out env group m isProject (declRangeExt.find? env ·) localConsts
  for e in Solidity.Goal.goalExt.getState env do
    out.putStrLn <| (Json.mkObj [("r", "goal"), ("g", toJson group),
      ("decl", toJson e.decl.toString), ("proof", toJson e.proof.toString),
      ("plan", toJson e.plan), ("deps", toJson (e.deps.map Name.toString))]).compress
  out.putStrLn <| (Json.mkObj [("r", "group-end"), ("g", toJson group),
    ("modules", toJson env.header.moduleNames.size)]).compress

def run : IO Unit := do
  let some outPath ← IO.getEnv "LEAN_INVENTORY_OUT" | return
  let some listPath ← IO.getEnv "LEAN_INVENTORY_MODULES"
    | throw <| IO.userError "LEAN_INVENTORY_MODULES is unset"
  initSearchPath (← findSysroot)
  let mut groups : Array (String × Array Name) := #[]
  let mut roots : Array (String × Name × String) := #[]
  for line in ← IO.FS.lines listPath do
    match line.splitOn "\t" with
    | [g, m] =>
      match groups.findIdx? (·.1 == g) with
      | some i => groups := groups.modify i fun (g', ms) => (g', ms.push m.toName)
      | none => groups := groups.push (g, #[m.toName])
    | [g, m, file] => roots := roots.push (g, m.toName, file)
    | _ => if line != "" then throw <| IO.userError s!"bad module line: {line}"
  let h ← IO.FS.Handle.mk outPath .write
  let out := IO.FS.Stream.ofHandle h
  out.putStrLn <| (Json.mkObj [("r", "header"), ("lean", toJson Lean.versionString),
    ("githash", toJson Lean.githash)]).compress
  for (g, ms) in groups do
    let env ← importModules (ms.map fun n => { module := n }) {} 0
    dumpEnv out g env
  for (g, m, file) in roots do
    let env ← elabRoot file m
    dumpEnv out g env (some m)
  out.putStrLn <| (Json.mkObj [("r", "end")]).compress
  out.flush

end Solidity.LeanInventory.Extract

#eval Solidity.LeanInventory.Extract.run
