import Solidity.Lowering.P8.GraphSchema
import Solidity.Lowering.P8.ScalarSchemaControls
import Solidity.Lowering.P8.ShapeSchemaControls

/-! Kernel controls for actual guarded recursive singleton extraction.
No source program/heap execution or full accepted admission is claimed. -/
namespace Solidity.Lowering.P8.GraphControls
open ScalarControls

def children : Source.Syn .structMember :=
  .structMember (.array (.userType ⟨"P8Node", []⟩) .none) "children"
def marker : Source.Syn (.list .structMember) :=
  .cons (.structMember (.elem .bool) "mark") .nil
def nodeDecl := decl "P8Node" children marker
def nodeResolution := resolution "P8Node" children marker

theorem core_wellFormed_node : Source.WellFormed nodeResolution := core_wellFormed _ _ _ rfl
theorem profile_node : Source.InProfileSyntax nodeResolution := rfl

def memory := (graphStruct nodeDecl rfl .memory).get (by decide +kernel)
def storage := (graphStruct nodeDecl rfl .storage).get (by decide +kernel)

theorem actual_memory_graph : Nonempty (V07.DeclarationGraph nodeResolution.env .memory memory.1) := ⟨memory.2⟩
theorem actual_storage_graph : Nonempty (V07.DeclarationGraph nodeResolution.env .storage storage.1) := ⟨storage.2⟩

theorem ordered_recursive_fields : memory.1.fields ⟨0, by decide⟩ =
    [("children", .array (.node ⟨0, by decide⟩)), ("mark", .prim .bool)] := by decide +kernel

theorem wrong_order : memory.1.fields ⟨0, by decide⟩ ≠
    [("mark", .prim .bool), ("children", .array (.node ⟨0, by decide⟩))] := by decide +kernel

theorem computed_rank : memory.1.rank ⟨0, by decide⟩ = 1 := by decide +kernel

def inlineField : Source.Syn .structMember := .structMember (.userType ⟨"P8Inline", []⟩) "self"
def inlineDecl := decl "P8Inline" inlineField .nil

theorem inline_core_wellFormed : Source.WellFormed (resolution "P8Inline" inlineField .nil) := core_wellFormed _ _ _ rfl

/-- Rejection by the graph's actual guardedness check exposes a necessary
admission obligation, never an invented approved-profile exclusion. -/
theorem inline_self_rejected : graphStruct inlineDecl rfl .storage = none := by rfl

def names : Fin 1 → Source.DeclName := fun _ => sourceName nodeDecl

theorem wrong_identity : findNode names ⟨none, "Different"⟩ = none := by decide +kernel

theorem wrong_scope : findNode names ⟨some "Foreign", "P8Node"⟩ = none := by decide +kernel

theorem unresolved_node_rejected : (encodeGraph nodeResolution.env.layout names
    (.struct .memory ⟨none, "Different"⟩)).map (·.target) = none := by decide +kernel

def fixedInlineField : Source.Syn .structMember :=
  .structMember (.array (.userType ⟨"P8FixedInline", []⟩) (.some (.lit (.num (.dec 2 0 0))))) "self"
def fixedInlineDecl := decl "P8FixedInline" fixedInlineField .nil

theorem fixed_inline_self_rejected : graphStruct fixedInlineDecl rfl .storage = none := rfl

theorem mapping_memory_rejected : graphStruct ShapeControls.mapDecl rfl .memory = none := rfl

/-- A fixed wrapper does not destroy the dynamic guard around a self node. -/
def guardedFixedField : Source.Syn .structMember :=
  .structMember (.array (.array (.userType ⟨"P8GuardedFixed", []⟩) .none)
    (.some (.lit (.num (.dec 2 0 0))))) "children"
def guardedFixedDecl := decl "P8GuardedFixed" guardedFixedField .nil

theorem guarded_fixed_wellFormed :
    Source.WellFormed (resolution "P8GuardedFixed" guardedFixedField .nil) :=
  core_wellFormed _ _ _ rfl

def guardedFixedMemory := (graphStruct guardedFixedDecl rfl .memory).get (by decide +kernel)
def guardedFixedStorage := (graphStruct guardedFixedDecl rfl .storage).get (by decide +kernel)

theorem guarded_fixed_memory_fields : guardedFixedMemory.1.fields ⟨0, by decide⟩ =
    [("children", .fixed (.array (.node ⟨0, by decide⟩)) ⟨2, by decide +kernel⟩)] := by decide +kernel

theorem guarded_fixed_storage_fields : guardedFixedStorage.1.fields ⟨0, by decide⟩ =
    [("children", .fixed (.array (.node ⟨0, by decide⟩)) ⟨2, by decide +kernel⟩)] := by decide +kernel

#print axioms guarded_fixed_memory_fields
#print axioms guarded_fixed_storage_fields

#print axioms actual_memory_graph
#print axioms actual_storage_graph
#print axioms inline_self_rejected
end Solidity.Lowering.P8.GraphControls
