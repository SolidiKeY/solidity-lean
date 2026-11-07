import Solidity.Lowering.P8.SourceAstParameterCorrespondence

/-! Mapping and function-type structural correspondence.
Regression purpose: retain mapping names/key/value and function parameter /
result lists, visibility and mutability through the unchanged readers. These
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

/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.optional_name_missing' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms optional_name_missing
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.optional_name_exact' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms optional_name_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.mapping_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_exact
/-- info: 'Solidity.Lowering.P8.SourceAstTypeCorrespondence.function_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms function_exact
end Solidity.Lowering.P8.SourceAstTypeCorrespondence
