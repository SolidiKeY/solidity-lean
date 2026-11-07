import Solidity.Lowering.P8.SourceAstParameterCorrespondence

/-! Leaf, mapping and function-type structural correspondence.
Regression purpose: retain mapping names/key/value and function parameter /
result lists, visibility and mutability through the unchanged readers. Leaf
paths retain explicit-node precedence and address payability. These
are syntax laws, not Source validity, artifact binding or execution proofs. -/
namespace Solidity.Lowering.P8.SourceAstTypeCorrespondence
open Lean Solidity.Source
open SourceAstExpressionCorrespondence

theorem optional_name_missing (node : Json) (field message : String)
    (missing : node.getObjVal? field = .error message) :
    SourceAstCompoundTypes.optionalName node field = .ok none := by
  unfold SourceAstCompoundTypes.optionalName
  rw [missing]
  rfl

theorem optional_name_exact (node : Json) (field name : String)
    (value : node.getObjVal? field = .ok (.str name)) :
    SourceAstCompoundTypes.optionalName node field =
      .ok (if name.isEmpty then none else some name) := by
  unfold SourceAstCompoundTypes.optionalName
  rw [value]
  rfl

/-- Key/value conversions and both optional mapping names are retained. -/
theorem mapping_exact (fuel : Nat) (node rawKey rawValue : Json)
    (key : MapKey) (value : Syn .typeName) (keyName valueName : Option String)
    (kind : node.getObjValAs? String "nodeType" = .ok "Mapping")
    (keyField : node.getObjVal? "keyType" = .ok rawKey)
    (keyValue : SourceAstCompoundTypes.mapKey rawKey = .ok key)
    (keyNameValue : SourceAstCompoundTypes.optionalName node "keyName" = .ok keyName)
    (valueField : node.getObjVal? "valueType" = .ok rawValue)
    (valueValue : SourceAstCompoundTypes.typeName fuel rawValue = .ok value)
    (valueNameValue : SourceAstCompoundTypes.optionalName node "valueName" = .ok valueName) :
    SourceAstCompoundTypes.typeName (fuel + 1) node = .ok (.mapping key keyName value valueName) := by
  rw [SourceAstCompoundTypes.typeName]
  simp only [kind, keyField, keyValue, keyNameValue, valueField, valueValue,
    valueNameValue, ok_bind]
  rfl

/-- Function-type results and qualifiers retain their converted identities.
The ordered list correspondence from C252 applies to both parameter readers. -/
theorem function_exact (fuel : Nat) (node rawArgs rawResults : Json)
    (args results : Syn (.list .param)) (visibility mutability : String)
    (vis : Option Visibility) (stateMut : Option Mutability)
    (kind : node.getObjValAs? String "nodeType" = .ok "FunctionTypeName")
    (argsField : node.getObjVal? "parameterTypes" = .ok rawArgs)
    (argsValue : SourceAstCompoundTypes.parametersWith (SourceAstCompoundTypes.typeName fuel)
      rawArgs = .ok args)
    (resultsField : node.getObjVal? "returnParameterTypes" = .ok rawResults)
    (resultsValue : SourceAstCompoundTypes.parametersWith (SourceAstCompoundTypes.typeName fuel)
      rawResults = .ok results)
    (visField : node.getObjValAs? String "visibility" = .ok visibility)
    (visValue : SourceAstCompoundTypes.visibility visibility = .ok vis)
    (mutField : node.getObjValAs? String "stateMutability" = .ok mutability)
    (mutValue : SourceAstCompoundTypes.mutability mutability = .ok stateMut) :
    SourceAstCompoundTypes.typeName (fuel + 1) node = .ok (.fnType args vis stateMut results) := by
  rw [SourceAstCompoundTypes.typeName]
  simp only [kind, argsField, argsValue, resultsField, resultsValue,
    visField, visValue, mutField, mutValue, ok_bind]
  rfl

/-- An explicit compiler path node takes precedence over fallback spelling. -/
theorem user_path_node_exact (node pathNode : Json) (written : String) (out : IdPath)
    (kind : node.getObjValAs? String "nodeType" = .ok "UserDefinedTypeName")
    (pathField : node.getObjVal? "pathNode" = .ok pathNode)
    (nameField : pathNode.getObjValAs? String "name" = .ok written)
    (converted : SourceAstTypes.path written = .ok out) :
    SourceAstTypes.typeNameLeaf node = .ok (.userType out) := by
  rw [SourceAstTypes.typeNameLeaf]
  simp only [kind, pathField, nameField, converted, ok_bind]
  rfl

/-- Fallback spelling is selected only when pathNode lookup fails. -/
theorem user_name_path_exact (node : Json) (message written : String) (out : IdPath)
    (kind : node.getObjValAs? String "nodeType" = .ok "UserDefinedTypeName")
    (pathMissing : node.getObjVal? "pathNode" = .error message)
    (nameField : node.getObjValAs? String "namePath" = .ok written)
    (converted : SourceAstTypes.path written = .ok out) :
    SourceAstTypes.typeNameLeaf node = .ok (.userType out) := by
  rw [SourceAstTypes.typeNameLeaf]
  simp only [kind, pathMissing, nameField, converted, ok_bind]
  rfl

/-- Non-address elementary types retain the exact existing width/name conversion. -/
theorem elementary_leaf_exact (node : Json) (name : String) (out : Elem)
    (kind : node.getObjValAs? String "nodeType" = .ok "ElementaryTypeName")
    (nameField : node.getObjValAs? String "name" = .ok name)
    (notAddress : (name == "address") = false)
    (converted : SourceAstTypes.elementary name = .ok out) :
    SourceAstTypes.typeNameLeaf node = .ok (.elem out) := by
  rw [SourceAstTypes.typeNameLeaf]
  simp only [kind, nameField, notAddress, converted, ok_bind, Bool.false_eq_true, ite_false]
  rfl

/-- Payability remains a distinct intrinsic elementary constructor. -/
theorem payable_address_exact (node : Json)
    (kind : node.getObjValAs? String "nodeType" = .ok "ElementaryTypeName")
    (nameField : node.getObjValAs? String "name" = .ok "address")
    (payable : node.getObjVal? "stateMutability" = .ok (.str "payable")) :
    SourceAstTypes.typeNameLeaf node = .ok (.elem .addressPayable) := by
  rw [SourceAstTypes.typeNameLeaf]
  simp only [kind, nameField, payable, ok_bind, beq_self_eq_true, ite_true]
  rfl

/-- Both existing nonpayable encodings retain plain address syntax. -/
theorem nonpayable_address_exact (node : Json)
    (kind : node.getObjValAs? String "nodeType" = .ok "ElementaryTypeName")
    (nameField : node.getObjValAs? String "name" = .ok "address")
    (plain : node.getObjVal? "stateMutability" = .ok (.str "nonpayable") ∨
      ∃ message, node.getObjVal? "stateMutability" = .error message) :
    SourceAstTypes.typeNameLeaf node = .ok (.elem .address) := by
  rcases plain with plain | ⟨message, plain⟩
  all_goals
    rw [SourceAstTypes.typeNameLeaf]
    simp only [kind, nameField, plain, ok_bind, beq_self_eq_true, ite_true]
    rfl

/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.user_path_node_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms user_path_node_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.user_name_path_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms user_name_path_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.elementary_leaf_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elementary_leaf_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.payable_address_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_address_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.nonpayable_address_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonpayable_address_exact

/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.optional_name_missing' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms optional_name_missing
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.optional_name_exact' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms optional_name_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.mapping_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.function_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms function_exact
end Solidity.Lowering.P8.SourceAstTypeCorrespondence
