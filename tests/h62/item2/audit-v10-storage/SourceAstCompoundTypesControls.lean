import Solidity.Lowering.P8.SourceAstCompoundTypes

/-! Structural conversion regressions, not Source acceptance/execution proofs.
Regression purpose: retain array bound and mapping names, nested function
parameter location, and explicit refusal of malformed/payable mapping keys. -/
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

def mappingShape : Syn .typeName → Bool
  | .mapping (.elem (.int false 256 _) _) (some "key")
      (.array (.elem .bool) (.some (.lit (.num (.dec 3 0 0))))) (some "values") => true
  | _ => false

def functionShape : Syn .typeName → Bool
  | .fnType (.cons (.param (.array (.elem .string) .none) (some .memory)
      (some "xs")) .nil) (some .external) (some .view) .nil => true
  | _ => false

def check : Except String Unit := do
  let bound ← Json.parse "{\"nodeType\":\"Literal\",\"kind\":\"number\",\"value\":\"3\"}"
  let mapping := Json.mkObj [("nodeType", .str "Mapping"),
    ("keyType", elementaryNode "uint256"), ("keyName", .str "key"),
    ("valueType", arrayNode (elementaryNode "bool") bound), ("valueName", .str "values")]
  unless mappingShape (← typeName 16 mapping) do throw "mapping/bound changed"
  let fn := Json.mkObj [("nodeType", .str "FunctionTypeName"),
    ("parameterTypes", params [parameterNode (arrayNode (elementaryNode "string") .null)]),
    ("returnParameterTypes", params []), ("visibility", .str "external"),
    ("stateMutability", .str "view")]
  unless functionShape (← typeName 16 fn) do throw "nested function parameter changed"
  for node in [mapping, fn] do
    unless !(typeName 1 node).isOk do throw "depth exhaustion ignored"
  let payableKey := Json.mkObj [("nodeType", .str "ElementaryTypeName"),
    ("name", .str "address"), ("stateMutability", .str "payable")]
  unless !(mapKey payableKey).isOk do throw "payable mapping key accepted"
  unless !(typeName 16 (arrayNode (elementaryNode "bool") (.str "bad bound"))).isOk do
    throw "malformed bound dropped"

#eval match check with
  | .ok _ => IO.println "compound type structure and refusal controls passed"
  | .error why => throw (IO.userError why)
end H62.StorageAudit.SourceAstCompoundTypesControls
