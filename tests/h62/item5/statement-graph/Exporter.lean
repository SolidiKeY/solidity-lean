import Lean

/-! H62 elaborated-type exporter. This optional tool is never imported by core.
Explicit selections permit read-only overlays on imported producer declarations.
Tags classify newly owned declarations; catalog metadata stays outside proofs. -/
open Lean Meta Elab Command
namespace H62
initialize statementTag : TagAttribute ← registerTagAttribute `h62_statement "Interface statement"
initialize premiseTag : TagAttribute ← registerTagAttribute `h62_premise "Named typed premise"
initialize helperTag : TagAttribute ← registerTagAttribute `h62_helper "Proof helper (not a statement edge)"

-- Overlay tags attach metadata to imported declarations without editing producers.
initialize overlayTags : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun rows row => rows.push row
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

def namesJson (ns : Array Name) : Json :=
  toJson ((ns.qsort Name.quickLt).map Name.toString)

def role (env : Environment) (n : Name) : String :=
  if let some (_, kind) := (overlayTags.getState env).find? (fun row => row.1 == n) then kind
  else if statementTag.hasTag env n then "statement"
  else if premiseTag.hasTag env n then "premise"
  else if helperTag.hasTag env n then "helper"
  else "unclassified"

structure CheckedWitness where
  consumer : Name
  scope : String
  index : Nat
  witness : Name
  helper : Name
  expectedType : Expr
  binderType : Expr
  priorBinders : Array String
  deriving Inhabited

initialize checkedWitnesses : SimplePersistentEnvExtension CheckedWitness (Array CheckedWitness) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun rows row => rows.push row
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

def registerWitness (consumer : Name) (scope : String) (index : Nat) (witness : Name) : MetaM Unit := do
  unless scope == "binder" || scope == "field" do throwError "unknown H62 witness scope"
  if (← getOptions).getBool `debug.skipKernelTC false then
    throwError "H62 witness requires kernel checking"
  if (checkedWitnesses.getState (← getEnv)).any (fun w => w.consumer == consumer && w.scope == scope && w.index == index) then
    throwError "duplicate H62 witness registration"
  let ci ← getConstInfo consumer
  let wi ← getConstInfo witness
  if wi.isUnsafe then throwError "unsafe H62 witness is forbidden"
  unless (← collectAxioms witness).isEmpty do throwError "H62 witness must be axiom-free"
  let mut targetType := ci.type
  let mut skip := 0
  if scope == "field" then
    let some _ := getStructureInfo? (← getEnv) consumer | throwError "H62 field target is not a structure"
    let .inductInfo info := ci | throwError "H62 field target is not inductive"
    let some ctor := info.ctors.head? | throwError "H62 field target has no constructor"
    targetType := (← getConstInfo ctor).type
    skip := info.numParams
  let absolute := skip + index
  let (expected, binderType, prior) ← forallTelescope targetType fun xs _ => do
    unless absolute < xs.size do throwError "H62 witness binder index is out of range"
    let ty ← inferType xs[absolute]!
    let preceding := xs[:absolute].toArray
    let expected ← mkForallFVars preceding ty
    let prior := (Array.range absolute).map fun i =>
      if scope == "binder" || i < skip then toString i else "field:" ++ toString (i - skip)
    return (expected, ty.abstract preceding, prior)
  -- Consumer universe parameters remain rigid; only witness universes are inferred.
  let value ← mkConstWithFreshMVarLevels witness
  unless ← isDefEq (← inferType value) expected do
    throwError "H62 witness type does not match the exact universal premise closure"
  let value ← instantiateMVars value
  let expected ← instantiateMVars expected
  if value.hasMVar || expected.hasMVar || value.hasFVar || expected.hasFVar then
    throwError "H62 witness is not closed or has unresolved metavariables"
  let helper := Name.str (`H62.CheckedWitness ++ consumer) (scope ++ "_" ++ toString index)
  if (← getEnv).contains helper then throwError "H62 witness helper name conflict"
  -- A safe declaration with the exact computed type is checked by Lean's kernel.
  addAndCompile <| .defnDecl {
    name := helper
    levelParams := ci.levelParams
    type := expected
    value := value
    hints := .opaque
    safety := .safe }
  unless (← collectAxioms helper).isEmpty do throwError "H62 checked helper is not axiom-free"
  modifyEnv fun env => checkedWitnesses.addEntry env {
    consumer := consumer, scope := scope, index := index, witness := witness, helper := helper,
    expectedType := expected, binderType := binderType, priorBinders := prior }

def witnessJson (consumer : Name) (scope : String) (index : Nat) : MetaM (Option Json) := do
  let entries := (checkedWitnesses.getState (← getEnv)).filter fun w =>
    w.consumer == consumer && w.scope == scope && w.index == index
  if entries.isEmpty then return none
  if entries.size != 1 then throwError "conflicting imported H62 witnesses"
  let w := entries[0]!
  let helper ← getConstInfo w.helper
  if helper.type != w.expectedType || helper.isUnsafe then
    throwError "H62 checked witness helper identity/type mismatch"
  return some <| Json.mkObj [
    ("consumer", toJson consumer.toString), ("scope", toJson scope), ("index", toJson index),
    ("declaration", toJson w.witness.toString), ("checkedDeclaration", toJson w.helper.toString),
    ("kernelChecked", toJson true), ("binderTypeExpr", toJson (reprStr w.binderType)),
    ("expectedTypeExpr", toJson (reprStr w.expectedType)), ("helperTypeExpr", toJson (reprStr helper.type)),
    ("priorBinders", toJson w.priorBinders), ("axioms", namesJson (← collectAxioms w.helper))]

def exportBinders (consumer : Name) (scope : String) (ty : Expr) (skip : Nat := 0) : MetaM (Array Json × Array Name) :=
  forallTelescope ty fun xs _ => do
    let mut rows : Array Json := #[]
    let mut refs : Array Name := #[]
    for i in [skip:xs.size] do
      let x := xs[i]!
      let d ← x.fvarId!.getDecl
      let ty ← instantiateMVars d.type
      refs := refs ++ ty.getUsedConstants
      let checked ← witnessJson consumer scope (i - skip)
      rows := rows.push <| Json.mkObj ([
        ("name", toJson d.userName.toString), ("contextSize", toJson i),
        ("type", toJson (← ppExpr ty).pretty),
        -- Close telescope locals using de Bruijn indices, never fresh FVarIds.
        ("typeExpr", toJson (reprStr (ty.abstract xs[:i].toArray))),
        ("isProp", toJson (← isProp ty)),
        ("references", namesJson ty.getUsedConstants)] ++
        (match checked with | some evidence => [("witness", evidence)] | none => []))
    return (rows, refs)

def exportDecl (n : Name) : MetaM Json := withOptions (fun o =>
    ((o.setBool `pp.fullNames true).setBool `pp.universes true).setBool `pp.notation false) do
  let ci ← getConstInfo n
  let env ← getEnv
  if (← getOptions).getBool `debug.skipKernelTC false then
    throwError "H62 export requires kernel checking"
  let mut kinds := (overlayTags.getState env).filterMap fun (decl, kind) =>
    if decl == n then some kind else none
  if statementTag.hasTag env n then kinds := kinds.push "statement"
  if premiseTag.hasTag env n then kinds := kinds.push "premise"
  if helperTag.hasTag env n then kinds := kinds.push "helper"
  if (kinds.toList.eraseDups).length > 1 then throwError "conflicting H62 tags on {n}"
  let mut typeRefs := ci.type.getUsedConstants
  let (binders, _) ← exportBinders n "binder" ci.type
  let mut fields : Array Json := #[]
  let mut fieldDecls : Array Name := #[]
  -- Structure contracts live in constructor/field types, not just `S : ... → Prop`.
  if let some info := getStructureInfo? env n then
    let .inductInfo induct := ci | throwError "structure {n} is not inductive"
    let some ctor := induct.ctors.head? | throwError "structure {n} has no constructor"
    let ctorInfo ← getConstInfo ctor
    let (fs, refs) ← exportBinders n "field" ctorInfo.type induct.numParams
    fields := fs
    typeRefs := typeRefs ++ refs
    fieldDecls := info.fieldInfo.map (·.projFn)
  typeRefs := typeRefs.toList.eraseDups.toArray
  for r in typeRefs ++ fieldDecls do
    unless env.contains r do throwError "missing type/field reference {r} in {n}"
  let proofRefs := match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  return Json.mkObj [
    ("declaration", toJson n.toString), ("role", toJson (role env n)),
    ("constantKind", toJson (match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor")),
    ("type", toJson (← ppExpr ci.type).pretty),
    ("typeExpr", toJson (reprStr ci.type)),
    ("typeReferences", namesJson typeRefs),
    ("taggedReferences", namesJson (typeRefs.filter fun r => role env r != "unclassified")),
    ("fieldDeclarations", namesJson fieldDecls),
    ("proofReferences", namesJson proofRefs),
    ("binders", toJson binders), ("fields", toJson fields),
    ("exists", toJson true),
    ("isTheorem", toJson (match ci with | .thmInfo _ => true | _ => false)),
    ("axioms", namesJson (← collectAxioms n))]

syntax (name := checkWitness) "#h62_witness " str ident num ident : command
elab_rules : command
  | `(#h62_witness $scope:str $consumer:ident $index:num $witness:ident) => do
    let target ← resolveGlobalConstNoOverload consumer
    let proof ← resolveGlobalConstNoOverload witness
    liftTermElabM <| registerWitness target scope.getString index.getNat proof

syntax (name := overlayTag) "#h62_tag " str ident : command
elab_rules : command
  | `(#h62_tag $kind:str $decl:ident) => do
    let k := kind.getString
    unless #["statement", "premise", "helper"].contains k do
      throwError "unknown H62 tag {k}"
    let n ← resolveGlobalConstNoOverload decl
    let existing := role (← getEnv) n
    unless existing == "unclassified" || existing == k do
      throwError "conflicting H62 overlay tag on {n}"
    modifyEnv fun env => overlayTags.addEntry env (n, k)

def writeExport (path : String) (names : Array Name) (scope : String) : CommandElabM Unit := do
  if names.size != (names.toList.eraseDups).length then
    throwError "duplicate declaration in H62 export"
  let rows : Array Json ← liftTermElabM <| (names.qsort Name.quickLt).mapM fun n => exportDecl n
  let some directory ← liftIO <| IO.getEnv "H62_GRAPH_OUTPUT_DIR"
    | throwError "H62_GRAPH_OUTPUT_DIR must name an off-git evidence directory"
  let target := System.FilePath.mk directory / path
  liftIO <| IO.FS.writeFile target ((Json.mkObj [
    ("schema", toJson 1), ("source", toJson "Lean.ConstantInfo.type"),
    ("scope", toJson scope), ("declarations", toJson rows)]).compress ++ "\n")

syntax (name := exportGraph) "#h62_export " str " [" ident,* "]" : command
elab_rules : command
  | `(#h62_export $path:str [$ns:ident,*]) => do
    let mut names : Array Name := #[]
    for n in ns.getElems do
      names := names.push (← resolveGlobalConstNoOverload n)
    writeExport path.getString names "explicit selected declarations; not a repository-wide census"

syntax (name := censusGraph) "#h62_census " str ident : command
elab_rules : command
  | `(#h62_census $path:str $ns:ident) => do
    let env ← getEnv
    let names := env.constants.toList.toArray.filterMap fun (name, _) =>
      if ns.getId.isPrefixOf ((privateToUserName? name).getD name) then some name else none
    if names.isEmpty then throwError "empty H62 namespace census: {ns.getId}"
    writeExport path.getString names s!"all elaborated declarations in namespace {ns.getId}; includes generated declarations"
end H62
