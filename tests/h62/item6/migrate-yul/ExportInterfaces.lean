import Lean

/-!
External inspection utility, not a proof or core module. Emits complete private
module declaration snapshots. Structural signatures, implementations, proofs,
and axiom unions remain separate evidence. No semantic equivalence is inferred.
-/
open Lean
namespace H62.MigrateYul.Export

def tag (s : String) (args : Array Json := #[]) : Json := .arr (#[.str s] ++ args)
def nameJson : Name → Json
  | .anonymous => tag "anonymous"
  | .str p s => tag "str" #[nameJson p, .str s]
  | .num p n => tag "num" #[nameJson p, toJson n]

def levelJson : Level → Except String Json
  | .zero => pure (tag "zero")
  | .succ l => do return tag "succ" #[← levelJson l]
  | .max l r => do return tag "max" #[← levelJson l, ← levelJson r]
  | .imax l r => do return tag "imax" #[← levelJson l, ← levelJson r]
  | .param n => pure (tag "param" #[nameJson n])
  | .mvar _ => throw "unexpected universe metavariable"

def binderJson : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

def exprJson : Expr → Except String Json
  | .bvar n => pure (tag "bvar" #[toJson n])
  | .fvar _ => throw "unexpected free variable"
  | .mvar _ => throw "unexpected expression metavariable"
  | .sort l => do return tag "sort" #[← levelJson l]
  | .const n ls => do return tag "const" #[nameJson n, .arr (← ls.toArray.mapM levelJson)]
  | .app f a => do return tag "app" #[← exprJson f, ← exprJson a]
  | .lam n t b bi => do return tag "lam" #[nameJson n, ← exprJson t, ← exprJson b, binderJson bi]
  | .forallE n t b bi => do return tag "forall" #[nameJson n, ← exprJson t, ← exprJson b, binderJson bi]
  | .letE n t v b nd => do return tag "let" #[nameJson n, ← exprJson t, ← exprJson v, ← exprJson b, toJson nd]
  | .lit (.natVal n) => pure (tag "nat" #[toJson n])
  | .lit (.strVal s) => pure (tag "string" #[.str s])
  | .mdata _ e => exprJson e
  | .proj n i e => do return tag "proj" #[nameJson n, toJson i, ← exprJson e]

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def namesJson (ns : List Name) : Json := .arr (ns.toArray.map nameJson)
def hintsJson : ReducibilityHints → Json
  | .opaque => tag "opaque"
  | .abbrev => tag "abbrev"
  | .regular d => tag "regular" #[toJson d.toNat]

def payload (ci : ConstantInfo) : Except String Json := do
  match ci with
  | .defnInfo v => return Json.mkObj [("implementation", .str (← exprJson v.value).compress), ("reducibility", hintsJson v.hints), ("mutual", namesJson v.all)]
  | .thmInfo v => return Json.mkObj [("proof", .str (← exprJson v.value).compress), ("mutual", namesJson v.all)]
  | .opaqueInfo v => return Json.mkObj [("implementation", .str (← exprJson v.value).compress), ("mutual", namesJson v.all)]
  | .inductInfo v => return Json.mkObj [("parameters", toJson v.numParams), ("indices", toJson v.numIndices), ("mutual", namesJson v.all), ("constructors", namesJson v.ctors), ("nested", toJson v.numNested), ("recursive", toJson v.isRec), ("reflexive", toJson v.isReflexive)]
  | .ctorInfo v => return Json.mkObj [("inductive", nameJson v.induct), ("index", toJson v.cidx), ("parameters", toJson v.numParams), ("fields", toJson v.numFields)]
  | .recInfo v =>
    let rules ← v.rules.toArray.mapM fun r => do
      return Json.mkObj [("constructor", nameJson r.ctor), ("fields", toJson r.nfields), ("rhs", .str (← exprJson r.rhs).compress)]
    return Json.mkObj [("mutual", namesJson v.all), ("parameters", toJson v.numParams), ("indices", toJson v.numIndices), ("motives", toJson v.numMotives), ("minors", toJson v.numMinors), ("k", toJson v.k), ("rules", .arr rules)]
  | .axiomInfo _ => return Json.mkObj []
  | .quotInfo v =>
    let q := match v.kind with
      | .type => "type"
      | .ctor => "constructor"
      | .lift => "lift"
      | .ind => "induction"
    return Json.mkObj [("quotient_kind", .str q)]

def declJson (moduleName originName : Name) (ci : ConstantInfo) : Except String Json := do
  return Json.mkObj [
    ("record", .str "declaration"), ("module", nameJson moduleName),
    ("authoritative_origin", nameJson originName), ("shared", toJson (originName != moduleName)),
    ("name", nameJson ci.name), ("display_name", .str ci.name.toString),
    ("kind", .str (kind ci)), ("private", toJson (isPrivateName ci.name)), ("universes", namesJson ci.levelParams),
    ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
    ("type", .str (← exprJson ci.type).compress), ("payload", ← payload ci)]

/-- External graph walk, following Lean.Util.CollectAxioms through private
kernel declarations. Also traverses recursor rules; missing constants fail. -/
def axiomUnion (env : Environment) (roots : Array Name) : IO (Array Name) := do
  let env := env.setExporting false
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut axioms : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n
      | throw (IO.userError ("missing axiom dependency: " ++ n.toString))
    pending := ci.type.getUsedConstants.toList ++ pending
    if let some value := ci.value? (allowOpaque := true) then
      pending := value.getUsedConstants.toList ++ pending
    match ci with
    | .axiomInfo _ => axioms := axioms.push n
    | .inductInfo v => pending := v.ctors ++ pending
    | .recInfo v =>
      for rule in v.rules do
        pending := rule.rhs.getUsedConstants.toList ++ pending
    | _ => pure ()
  return axioms.qsort fun a b => (nameJson a).compress < (nameJson b).compress

def run (moduleString output : String) : IO Unit := do
  initSearchPath (← findSysroot)
  let parts := moduleString.splitOn "."
  if parts.any String.isEmpty then throw (IO.userError "empty module-name component")
  let moduleName := parts.foldl (fun n part => Name.str n part) Name.anonymous
  let env ← importModules #[{module := moduleName, importAll := true}] {} (level := .private)
  let some idx := env.getModuleIdx? moduleName | throw (IO.userError "missing module provenance")
  let some effective := env.header.modules[idx]? | throw (IO.userError "missing effective import")
  unless effective.importAll do throw (IO.userError "private/import-all data not loaded")
  let some data := env.header.moduleData[idx]? | throw (IO.userError "missing module data")
  let rows := data.constants.toList.map fun ci => (ci.name, ci)
  let rows := rows.toArray.qsort fun a b => (nameJson a.1).compress < (nameJson b.1).compress
  let mut actual : NameSet := {}
  for (n, _) in rows do
    if actual.contains n then throw (IO.userError "duplicate declaration")
    actual := actual.insert n
  for n in data.constNames do
    unless actual.contains n do throw (IO.userError ("missing declaration: " ++ n.toString))
  let out ← IO.FS.Handle.mk output .write
  out.putStrLn (Json.mkObj [("record", .str "header"), ("schema", toJson (2 : Nat)), ("expression_encoding", .str "tagged structural Expr JSON text, metadata erased only"), ("module", nameJson moduleName), ("import_level", .str "private"), ("import_all", toJson true), ("participates_module_system", toJson data.isModule), ("expected_constants", toJson data.constNames.size), ("extra_codegen_count", toJson data.extraConstNames.size), ("extra_codegen_names", .arr (data.extraConstNames.map nameJson)), ("extra_codegen_scope", .str "IR-only names; not kernel ConstantInfo declarations"), ("limitation", .str "Structural snapshots are not semantic equivalence, proof replay or attribute/instance-priority validation.")]).compress
  let mut roots := rows.map (·.1)
  let mut directAxioms : Array Name := #[]
  for (_, ci) in rows do
    let some originIdx := env.getModuleIdxFor? ci.name
      | throw (IO.userError ("missing authoritative provenance: " ++ ci.name.toString))
    let some originName := env.header.moduleNames[originIdx]?
      | throw (IO.userError "missing authoritative module")
    roots := roots ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      roots := roots ++ value.getUsedConstants
    match ci with
    | .axiomInfo _ => directAxioms := directAxioms.push ci.name
    | .inductInfo v => roots := roots ++ v.ctors.toArray
    | .recInfo v =>
      for rule in v.rules do roots := roots ++ rule.rhs.getUsedConstants
    | _ => pure ()
    match declJson moduleName originName ci with
    | .ok row => out.putStrLn row.compress
    | .error msg => throw (IO.userError (ci.name.toString ++ ": " ++ msg))
  let collected ← axiomUnion env roots
  let mut axSeen : NameSet := {}
  let mut axioms : Array Name := #[]
  for n in collected ++ directAxioms do
    unless axSeen.contains n do
      axSeen := axSeen.insert n
      axioms := axioms.push n
  axioms := axioms.qsort fun a b => (nameJson a).compress < (nameJson b).compress
  out.putStrLn (Json.mkObj [("record", .str "complete"), ("module", nameJson moduleName), ("count", toJson rows.size), ("axiom_union", .arr (axioms.map nameJson))]).compress
  out.flush
  IO.println s!"exported {moduleString}: {rows.size} declarations"
def selfTest : IO Unit := do
  let expectFailure (r : Except String Json) : IO Unit :=
    match r with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "invalid expression accepted")
  expectFailure (exprJson (.fvar ⟨`bad⟩))
  expectFailure (exprJson (.mvar ⟨`bad⟩))
  expectFailure (levelJson (.mvar ⟨`bad⟩))
  let a := (nameJson (.str .anonymous "a.b")).compress
  let b := (nameJson (.str (.str .anonymous "a") "b")).compress
  if a == b then throw (IO.userError "ambiguous name serialization")
  let e := Expr.forallE `x (.sort .zero) (.bvar 0) .default
  let encode (e : Expr) : IO String :=
    match exprJson e with
    | .ok j => pure j.compress
    | .error msg => throw (IO.userError msg)
  let plain ← encode e
  let metadata ← encode (.mdata MData.empty e)
  let implicitBinder ← encode (.forallE `x (.sort .zero) (.bvar 0) .implicit)
  if plain != metadata then throw (IO.userError "metadata normalization failed")
  if plain == implicitBinder then throw (IO.userError "binder annotation lost")
  IO.println "interface serializer controls: PASS"
end H62.MigrateYul.Export

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => H62.MigrateYul.Export.selfTest; return 0
  | [moduleName, output] => H62.MigrateYul.Export.selfTest; H62.MigrateYul.Export.run moduleName output; return 0
  | _ => throw (IO.userError "usage: ExportInterfaces MODULE OUTPUT.jsonl.partial")
