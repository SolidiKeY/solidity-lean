import Solidity.Lowering.P8.SourceAstUnit
import Solidity.Source.WellFormed

/-! Conversion/resolution checks independent of the pending full-elaboration
acceptance probe. Regression purpose: preserve the same eight owned catalogue
entries in both actual pipeline inputs. No body typing or origin is claimed. -/
namespace H62.StorageAudit.SourceAstUnitControls
open Lean Solidity.Source
open Solidity.Lowering.P8.SourceAstUnit

def fixtureInputs : List (String × Solidity.Roadmap.Pipeline) :=
  [("tests/solc/LibraryTry.ast.json", .legacy), ("tests/solc/LibraryTryIR.ast.json", .viaIR)]

def inspect (doc : Json) (pipeline : Solidity.Roadmap.Pipeline) : Except String Resolution := do
  let converted ← unit 128 (← doc.getObjVal? "ast")
  let result := resolveUnit { pipeline := pipeline } converted
  let declarations := result.env.decls
  for (scope, name, kind) in [(none, "L", DeclKind.library), (none, "C", .contract),
      (some "L", "S", .struct), (some "L", "integer", .function),
      (some "L", "stru", .function), (some "C", "t", .stateVar),
      (some "C", "f", .function), (some "C", "g", .function)] do
    unless (declarations.filter (fun d => d.scope == scope && d.name == name && d.kind == kind)).length == 1 do
      throw "source declaration ownership changed"
  unless declarations.length == 8 do throw "unexpected Source declaration count"
  return result

#eval do
  for (file, pipeline) in fixtureInputs do
    let raw ← IO.FS.readFile file
    match (do inspect (← Json.parse raw) pipeline) with
    | .ok _ => IO.println s!"{file}: complete unit conversion and eight Source identities passed"
    | .error why => throw (IO.userError why)
end H62.StorageAudit.SourceAstUnitControls
