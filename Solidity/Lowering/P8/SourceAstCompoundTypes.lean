import Solidity.Lowering.P8.SourceAstExpressions

/-! Recursive compiler type syntax, without a second type representation.
Regression purpose: preserve nested arrays, mapping names and function-type
parameter qualifiers before Source resolution. Conversion fuel is not Source
execution fuel. This reader establishes no accepted-program or H24 claim. -/
namespace Solidity.Lowering.P8.SourceAstCompoundTypes
open Lean Solidity.Source
open SourceAstParameters

/-- Share parameter structure while supplying the recursive type reader. -/
def parameterWith (readType : Json → Except String (Syn .typeName))
    (node : Json) : Except String (Syn .param) := do
  unless (← node.getObjValAs? String "nodeType") == "VariableDeclaration" do
    throw "parameter declaration required"
  let ty ← readType (← node.getObjVal? "typeName")
  let loc ← SourceAstTypes.location (← node.getObjValAs? String "storageLocation")
  let name ← node.getObjValAs? String "name"
  return .param ty loc (if name.isEmpty then none else some name)

def parametersWith (readType : Json → Except String (Syn .typeName))
    (node : Json) : Except String (Syn (.list .param)) := do
  unless (← node.getObjValAs? String "nodeType") == "ParameterList" do
    throw "parameter list required"
  let nodes ← node.getObjValAs? (Array Json) "parameters"
  return syntaxList (← nodes.toList.mapM (parameterWith readType))

def optionalName (node : Json) (key : String) : Except String (Option String) := do
  match node.getObjVal? key with
  | .error _ => return none
  | .ok value =>
    let name ← value.getStr?
    return if name.isEmpty then none else some name

def mapKey (node : Json) : Except String MapKey := do
  match ← SourceAstTypes.typeNameLeaf node with
  | .userType path => return .path path
  | .elem value =>
    if h : value = .addressPayable then throw "payable mapping key is not grammar syntax"
    else return .elem value h
  | _ => throw "mapping key syntax required"

def visibility (name : String) : Except String (Option Visibility) :=
  match name with
  | "internal" => .ok (some .internal)
  | "external" => .ok (some .external)
  | _ => .error "function type visibility required"

def mutability (name : String) : Except String (Option Mutability) :=
  match name with
  | "nonpayable" => .ok none
  | "view" => .ok (some .view)
  | "pure" => .ok (some .pure)
  | "payable" => .ok (some .payable)
  | _ => .error "function type mutability required"

/-- Compound nodes recurse; leaves reuse the already checked leaf reader.
Array lengths use the expression reader instead of discarding fixed bounds. -/
def typeName : Nat → Json → Except String (Syn .typeName)
  | 0, _ => .error "type conversion depth exhausted"
  | fuel + 1, node => do
    match ← node.getObjValAs? String "nodeType" with
    | "ArrayTypeName" =>
      let base ← typeName fuel (← node.getObjVal? "baseType")
      let length ← node.getObjVal? "length"
      let bound : Syn (.opt .expr) ← match length with
        | .null => pure (Syn.none : Syn (.opt .expr))
        | _ => (SourceAstExpressions.expression fuel length).map Syn.some
      return .array base bound
    | "Mapping" =>
      return .mapping (← mapKey (← node.getObjVal? "keyType"))
        (← optionalName node "keyName") (← typeName fuel (← node.getObjVal? "valueType"))
        (← optionalName node "valueName")
    | "FunctionTypeName" =>
      let args ← parametersWith (typeName fuel) (← node.getObjVal? "parameterTypes")
      let results ← parametersWith (typeName fuel) (← node.getObjVal? "returnParameterTypes")
      return .fnType args (← visibility (← node.getObjValAs? String "visibility"))
        (← mutability (← node.getObjValAs? String "stateMutability")) results
    | _ => SourceAstTypes.typeNameLeaf node

theorem parameterWith_leaf (node : Json) :
    parameterWith SourceAstTypes.typeNameLeaf node = SourceAstTypes.parameter node := rfl

theorem zero_depth (node : Json) :
    typeName 0 node = .error "type conversion depth exhausted" := rfl

/-- info: 'Solidity.Lowering.P8.SourceAstCompoundTypes.parameterWith_leaf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms parameterWith_leaf
/-- info: 'Solidity.Lowering.P8.SourceAstCompoundTypes.zero_depth' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms zero_depth
/-- info: 'Solidity.Lowering.P8.SourceAstCompoundTypes.typeName' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms typeName
end Solidity.Lowering.P8.SourceAstCompoundTypes
