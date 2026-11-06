import Solidity.Lowering.P8.ShapeSchema
import Solidity.Lowering.P8.ScalarSchemaControls

/-! Actual resolved structured-field clients and boundary controls. These are
shape certificates only, not parser/compiler/value execution theorems. -/
namespace Solidity.Lowering.P8.ShapeControls
open ScalarControls

def nestedField : Source.Syn .structMember :=
  .structMember (.array (.array (.elem .bool) .none) .none) "children"
def nestedDecl := decl "P8Nested" nestedField .nil
def nestedResolution := resolution "P8Nested" nestedField .nil

theorem nested_core_wellFormed : Source.WellFormed nestedResolution :=
  core_wellFormed _ _ _ rfl
theorem nested_profile : Source.InProfileSyntax nestedResolution := rfl

def nested := (shapeStruct nestedDecl rfl .memory).get (by decide +kernel)

theorem nested_actual_graph : Nonempty (V07.DeclarationGraph nestedResolution.env .memory nested.1) :=
  ⟨nested.2⟩
theorem nested_fields : nested.1.fields ⟨0, by decide⟩ =
    [("children", .array (.array (.prim .bool)))] := by decide +kernel

theorem wrong_element : nested.1.fields ⟨0, by decide⟩ ≠
    [("children", .array (.array (.prim .uint)))] := by decide +kernel

theorem wrong_nesting : nested.1.fields ⟨0, by decide⟩ ≠
    [("children", .array (.prim .bool))] := by decide +kernel

def mapField : Source.Syn .structMember := .structMember
  (.mapping (.elem (.int false 8 (by decide)) (by decide)) none (.array (.elem .bool) .none) none) "rows"
def mapDecl := decl "P8Map" mapField .nil
def mapResolution := resolution "P8Map" mapField .nil

theorem mapping_core_wellFormed : Source.WellFormed mapResolution := core_wellFormed _ _ _ rfl
theorem mapping_profile : Source.InProfileSyntax mapResolution := rfl

def mapping := (shapeStruct mapDecl rfl .storage).get (by decide +kernel)

theorem mapping_actual_graph : Nonempty (V07.DeclarationGraph mapResolution.env .storage mapping.1) :=
  ⟨mapping.2⟩
theorem mapping_fields : mapping.1.fields ⟨0, by decide⟩ =
    [("rows", .mapping .uint (.array (.prim .bool)))] := by decide +kernel

/-- Actual source memory field resolution refuses mappings; storage success
must not be reused as a memory-location certificate. -/
theorem mapping_memory_rejected : shapeStruct mapDecl rfl .memory = none := rfl

def names : Fin 1 → Source.DeclName := fun _ => sourceName nestedDecl

def fixedCode := encodeShape nestedResolution.env.layout names (.array .storage .bool (some 2))
theorem fixed_shape : fixedCode.map (·.target) =
    some (.fixed (.prim .bool) ⟨2, by decide⟩) := by decide +kernel
theorem fixed_height : fixedCode.map (·.height) = some 1 := by decide +kernel

theorem zero_fixed_rejected : encodeShape nestedResolution.env.layout names
    (.array .storage .bool (some 0)) = none := rfl

theorem word_limit_fixed_rejected : encodeShape nestedResolution.env.layout names
    (.array .storage .bool (some (2^256))) = none := rfl

theorem duplicate_shape_rejected : shapeStruct (decl "P8Record" first duplicateRest) rfl .storage = none := rfl

/-- Recursive struct nodes are still OPEN in this producer, not an exclusion. -/
theorem node_still_open : encodeShape nestedResolution.env.layout names
    (.struct .memory (sourceName nestedDecl)) = none := rfl

#print axioms nested_actual_graph
#print axioms mapping_actual_graph
#print axioms fixed_shape
#print axioms mapping_memory_rejected
end Solidity.Lowering.P8.ShapeControls
