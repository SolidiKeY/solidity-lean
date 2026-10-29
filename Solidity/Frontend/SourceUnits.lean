import Solidity.Frontend.Source

/-!
# Original source units at the compiler boundary

Schema 2 stores a complete, named set of original solc SourceUnit ASTs. The
selected unit is separate from the dependency set: neither a concatenated AST
nor a single-source provenance record stands in for the compilation. Imports
are resolved by solc; this boundary checks their source-unit identities and
resolved paths, including cycles, against the recorded finite source set.
-/

namespace Solidity.Frontend.Source
open Lean (Json toJson)

structure CompilationUnit where
  primary : Json
  asts : List Json
  provenance : Provenance

private def keys (j : Json) (allowed : List String) : Bool :=
  match j with
  | .obj fields => fields.toList.all fun (key, _) => allowed.contains key
  | _ => false

private def field (j : Json) (key : String) : Json :=
  (j.getObjVal? key).toOption.getD .null

/-- Validate every original location and import before any dependency is lowered.
The budget is derived from the input size, not a configurable search limit. -/
private def checkTree (sources : List SourceFile) (sourceId : Nat) (mixedAbiInheritance : Bool := false) :
    Nat → Json → Except String Unit
  | 0, _ => throw "compilation-unit AST depth bound exhausted"
  | fuel + 1, j => do
    if sources.length > 1 then
      let doc := field j "documentation"
      let text := doc.getStr?.toOption.getD ((doc.getObjValAs? String "text").toOption.getD "")
      if (text.splitOn "@custom:key").length > 1 ||
          (j.getObjVal? "loopSpec").isOk then
        throw "solidity.compilationUnitSpecifications: source specifications require file-local lexical resolution"
    if mixedAbiInheritance &&
        (j.getObjValAs? String "nodeType").toOption == some "InheritanceSpecifier" then
      throw "solidity.compilationUnitAbiModes: inherited entries with mixed legacy ABI modes require a declaring-source adapter"
    if (j.getObjVal? "nodeType").isOk then
      let src ← j.getObjValAs? String "src"
      match src.splitOn ":" with
      | [start, size, file] =>
        unless start.toNat?.isSome && size.toNat?.isSome && file.toNat? == some sourceId do
          throw "foreign or malformed compilation-unit source location"
      | _ => throw "malformed compilation-unit source location"
      if (j.getObjValAs? String "nodeType").toOption == some "ImportDirective" then
        let path ← j.getObjValAs? String "absolutePath"
        let target ← j.getObjValAs? Nat "sourceUnit"
        unless sources.any (fun source => source.name == path && source.declarationId == target) do
          throw "import target is absent or disagrees with compilation-unit provenance"
    match j with
    | .arr values => for value in values do checkTree sources sourceId mixedAbiInheritance fuel value
    | .obj fields => for (_, value) in fields.toList do checkTree sources sourceId mixedAbiInheritance fuel value
    | _ => pure ()

/-- Schema 1 and historical inputs retain their exact admission boundary.
Schema 2 cannot fall back to a single-source interpretation. -/
def readCompilationUnit (fixture : Json) : Except String CompilationUnit := do
  let header ← fixture.getObjVal? "header"
  if (header.getObjValAs? Nat "provenanceVersion").toOption != some 2 then
    unless !(fixture.getObjVal? "sourceUnits").isOk do
      throw "source units require compilation-unit provenance schema 2"
    let primary ← fixture.getObjVal? "ast"
    let provenance ← read fixture primary
    if !provenance.legacyFixture then
      if ((field primary "nodes").getArr?.toOption.getD #[]).any (fun node =>
          (node.getObjValAs? String "nodeType").toOption == some "ImportDirective") then
        throw "imports require complete compilation-unit provenance"
      let src ← primary.getObjValAs? String "src"
      let some sourceId := (src.splitOn ":").getLast?.bind String.toNat?
        | throw "malformed single-source compiler identity"
      let declarationId ← primary.getObjValAs? Nat "id"
      let source : SourceFile := {
        name := provenance.source, sourceId, declarationId
        sourceSha256 := provenance.sourceSha256
        requestedCoder := provenance.requestedCoder, gates := provenance.gates }
      checkTree [source] sourceId false (primary.compress.length + 1) primary
    return { primary, asts := [primary], provenance }
  unless keys fixture ["header", "sourceUnits"] &&
      keys header ["solcVersion", "solkeyCommit", "provenanceVersion", "compilerFile",
        "compilerSha256", "validationStage", "settings", "mainSource"] do
    throw "unknown compilation-unit provenance field"
  let main ← header.getObjValAs? String "mainSource"
  let inputs ← fixture.getObjValAs? (Array Json) "sourceUnits"
  unless !main.isEmpty && inputs.size > 1 do
    throw "compilation-unit provenance requires a main source and multiple source units"
  let mut asts : List Json := []
  let mut sources : List SourceFile := []
  let mut primary : Option (Json × Provenance) := none
  for input in inputs do
    unless keys input ["name", "id", "sourceSha256", "acceptedPragmas", "ast"] do
      throw "unknown source-unit provenance field"
    let name ← input.getObjValAs? String "name"
    let sourceId ← input.getObjValAs? Nat "id"
    let ast ← input.getObjVal? "ast"
    let declarationId ← ast.getObjValAs? Nat "id"
    unless !name.isEmpty && (← ast.getObjValAs? String "absolutePath") == name do
      throw "source-unit name disagrees with its compiler AST"
    if sources.any (fun source => source.name == name || source.sourceId == sourceId ||
        source.declarationId == declarationId) then
      throw "duplicate source-unit name or compiler identity"
    let unitHeader := Json.mkObj [
      ("solcVersion", field header "solcVersion"), ("solkeyCommit", field header "solkeyCommit"),
      ("source", toJson name), ("sourceSha256", field input "sourceSha256"),
      ("provenanceVersion", toJson (1 : Nat)), ("compilerFile", field header "compilerFile"),
      ("compilerSha256", field header "compilerSha256"),
      ("validationStage", field header "validationStage"), ("settings", field header "settings"),
      ("acceptedPragmas", field input "acceptedPragmas")]
    let provenance ← read (Json.mkObj [("header", unitHeader)]) ast true
    sources := sources ++ [{
      name, sourceId, declarationId
      sourceSha256 := provenance.sourceSha256
      requestedCoder := provenance.requestedCoder
      gates := provenance.gates }]
    asts := asts ++ [ast]
    if name == main then primary := some (ast, provenance)
  let some (ast, provenance) := primary | throw "main source is absent from the compilation unit"
  for input in inputs do
    let sourceId ← input.getObjValAs? Nat "id"
    let original ← input.getObjVal? "ast"
    checkTree sources sourceId
      (provenance.pipeline == some .legacy && sources.any (·.requestedCoder != provenance.requestedCoder))
      (original.compress.length + 1) original
  return { primary := ast, asts, provenance := { provenance with sources } }

/-- Source language modes follow compiler source identity, including dependencies. -/
def Provenance.atNode (provenance : Provenance) (node : Json) : Provenance :=
  let sourceId := ((node.getObjValAs? String "src").toOption.bind fun src =>
    (src.splitOn ":").getLast?.bind String.toNat?)
  match provenance.sources.find? (fun source => some source.sourceId == sourceId) with
  | none => provenance
  | some source => { provenance with
      source := source.name
      sourceSha256 := source.sourceSha256
      requestedCoder := source.requestedCoder
      gates := source.gates }

end Solidity.Frontend.Source
