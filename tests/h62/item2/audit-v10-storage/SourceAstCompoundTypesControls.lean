import Solidity.Lowering.P8.SourceAstTypeCorrespondence

/-! Structural conversion regressions, not Source acceptance/execution proofs.
Regression purpose: retain array bound and mapping names, nested function
parameter location, anonymous/named qualifiers, nonempty function results
and function qualifiers, and explicit refusal of malformed/payable mapping keys. -/
namespace H62.StorageAudit.SourceAstCompoundTypesControls
open Lean Solidity.Source Solidity.Lowering.P8.SourceAstCompoundTypes

def elementaryNode (name : String) : Json := Json.mkObj [
  ("nodeType", .str "ElementaryTypeName"), ("name", .str name)]
def arrayNode (base length : Json) : Json := Json.mkObj [
  ("nodeType", .str "ArrayTypeName"), ("baseType", base), ("length", length)]
def parameterNode (ty : Json) : Json := Json.mkObj [
  ("nodeType", .str "VariableDeclaration"), ("typeName", ty),
  ("name", .str "xs"), ("storageLocation", .str "memory")]
def params (values : List Json) : Json := Json.mkObj [
  ("nodeType", .str "ParameterList"), ("parameters", .arr values.toArray)]

def functionNode (results : Json) (visibility stateMutability : String) : Json :=
  Json.mkObj [("nodeType", .str "FunctionTypeName"),
    ("parameterTypes", params [parameterNode (arrayNode (elementaryNode "string") .null)]),
    ("returnParameterTypes", results), ("visibility", .str visibility),
    ("stateMutability", .str stateMutability)]

def mappingShape : Syn .typeName → Bool
  | .mapping (.elem (.int false 256 _) _) (some "key")
      (.array (.elem .bool) (.some (.lit (.num (.dec 3 0 0))))) (some "values") => true
  | _ => false

def functionShape : Syn .typeName → Bool
  | .fnType (.cons (.param (.array (.elem .string) .none) (some .memory)
      (some "xs")) .nil) (some .external) (some .view) .nil => true
  | _ => false

def parameterShape (expectedName : Option String) (expectedLoc : Option DataLoc) : Syn .param → Bool
  | .param (.elem (.int false 256 _)) loc name => decide (loc = expectedLoc ∧ name = expectedName)
  | _ => false

def check : Except String Unit := do
  let bound ← Json.parse "{\"nodeType\":\"Literal\",\"kind\":\"number\",\"value\":\"3\"}"
  let mapping := Json.mkObj [("nodeType", .str "Mapping"),
    ("keyType", elementaryNode "uint256"), ("keyName", .str "key"),
    ("valueType", arrayNode (elementaryNode "bool") bound), ("valueName", .str "values")]
  unless mappingShape (← typeName 16 mapping) do throw "mapping/bound changed"
  let fn := functionNode (params []) "external" "view"
  unless functionShape (← typeName 16 fn) do throw "nested function parameter changed"
  for node in [mapping, fn] do
    unless !(typeName 1 node).isOk do throw "depth exhaustion ignored"
  let payableKey := Json.mkObj [("nodeType", .str "ElementaryTypeName"),
    ("name", .str "address"), ("stateMutability", .str "payable")]
  unless !(mapKey payableKey).isOk do throw "payable mapping key accepted"
  unless !(typeName 16 (arrayNode (elementaryNode "bool") (.str "bad bound"))).isOk do
    throw "malformed bound dropped"

  -- Syntax-only qualifier preservation; scalar storage/calldata combinations
  -- are not asserted to be valid Source programs.
  for (name, loc, expectedName, expectedLoc) in [
      ("", "default", none, none), ("value", "storage", some "value", some DataLoc.storage),
      ("value", "calldata", some "value", some DataLoc.calldata)] do
    let node := Json.mkObj [("nodeType", .str "VariableDeclaration"),
      ("typeName", elementaryNode "uint256"), ("name", .str name), ("storageLocation", .str loc)]
    unless parameterShape expectedName expectedLoc (← parameterWith (typeName 16) node) do
      throw "parameter name or qualifier changed"

  -- Guard a real result list and qualifier alternatives, not just empty returns.
  for (vis, stateMut, expectedVis, expectedMut) in [
      ("internal", "nonpayable", Visibility.internal, (none : Option Mutability)),
      ("external", "payable", Visibility.external, some Mutability.payable)] do
    let signature := functionNode (params [parameterNode (elementaryNode "string")]) vis stateMut
    match ← typeName 16 signature with
    | .fnType _ actualVis actualMut
        (.cons (.param (.elem .string) (some .memory) (some "xs")) .nil) =>
      unless decide (actualVis = some expectedVis ∧ actualMut = expectedMut) do
        throw "function qualifier changed"
    | _ => throw "function result list changed"

#eval match check with
  | .ok _ => IO.println "compound type structure and refusal controls passed"
  | .error why => throw (IO.userError why)
end H62.StorageAudit.SourceAstCompoundTypesControls
