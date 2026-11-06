import Solidity.Lowering.V07.PrimitiveGraph
import Solidity.Lowering.V07.GraphIdentityControls

namespace Solidity.Lowering.V07.PrimitiveGraphControls
open PrimitiveGraph

def skip : Source.Decl := ⟨.enum,"Marker",none,true,.enum "Marker" "Only" []⟩
def env : Source.Env := ⟨[skip,GraphIdentityControls.declaration "Left",
  GraphIdentityControls.declaration "Right"]⟩

theorem two_nodes : (nodes env).length = 2 := rfl

theorem actual_source_positions :
    (index env ⟨0,by decide⟩).val = 1 ∧ (index env ⟨1,by decide⟩).val = 2 := by decide

theorem unique : UniqueNames env := by decide

theorem fields_ok (loc : Source.DataLoc) : FieldsOK env loc := by
  cases loc <;> decide

theorem computed_success (loc : Source.DataLoc) :
    (produce "actual-source-primitive-fields" env loc).isSome = true := by
  cases loc <;> decide

def result (loc : Source.DataLoc) :=
  (produce "actual-source-primitive-fields" env loc).get (computed_success loc)

theorem equal_fields_distinct_identity (loc : Source.DataLoc) :
    (result loc).1.fields ⟨0,by decide⟩ = (result loc).1.fields ⟨1,by decide⟩ ∧
    (result loc).1.declId ⟨0,by decide⟩ ≠ (result loc).1.declId ⟨1,by decide⟩ := by
  cases loc <;> decide

theorem complete_actual_declarations (loc : Source.DataLoc) :
    ∀ j : Fin env.decls.length, env.decls[j].kind = .struct →
      ∃ i, (result loc).2.sourceIndex i = j := (result loc).2.complete

theorem actual_layout_left : env.layout.fields ⟨none,"Left"⟩ = [.int .u8] :=
  memory_layout "actual-source-primitive-fields" env unique (fields_ok .memory) ⟨0,by decide⟩

def scopedDecl (scope : String) : Source.Decl :=
  ⟨.struct,"Cell",some scope,false,
    .struct "Cell" (.structMember (.elem .bool) "ready") .nil⟩
def scopedEnv : Source.Env := ⟨[scopedDecl "Left",scopedDecl "Right"]⟩

theorem scopes_preserved :
    name scopedEnv ⟨0,by decide⟩ ≠ name scopedEnv ⟨1,by decide⟩ ∧
    (produce "scoped" scopedEnv .storage).isSome = true := by decide

def duplicated : Source.Env := ⟨[GraphIdentityControls.declaration "Same",
  GraphIdentityControls.declaration "Same"]⟩

theorem duplicate_identity_rejected :
    (produce "duplicate" duplicated .storage).isNone = true := by decide

def byteDecl : Source.Decl :=
  ⟨.struct,"ByteCell",none,true,
    .struct "ByteCell" (.structMember (.elem .bytes) "data") .nil⟩
def byteEnv : Source.Env := ⟨[byteDecl]⟩

theorem bytes_source_resolves :
    byteEnv.structFields ⟨none,"ByteCell"⟩ .memory = some [("data",.bytes .memory)] := rfl

theorem bytes_component_open :
    (produce "unsupported-is-not-source-rejection" byteEnv .memory).isNone = true := by decide

def repeatedField : Source.Decl :=
  ⟨.struct,"Repeated",none,true,
    .struct "Repeated" (.structMember (.elem .bool) "same")
      (.cons (.structMember (.elem .address) "same") .nil)⟩
def repeatedEnv : Source.Env := ⟨[repeatedField]⟩

theorem duplicate_field_rejected :
    (produce "duplicate-field" repeatedEnv .storage).isNone = true := by decide

theorem collapsed_source_position_wrong :
    (result .storage).1.declId ⟨0,by decide⟩ ≠ 0 := by decide

def mixedDecl : Source.Decl :=
  ⟨.struct,"Mixed",none,true,
    .struct "Mixed" (.structMember (.elem (.int true 16 (by decide))) "delta")
      (.cons (.structMember (.elem .addressPayable) "recipient")
        (.cons (.structMember (.elem .bool) "ready") .nil))⟩
def mixedEnv : Source.Env := ⟨[mixedDecl]⟩

theorem mixed_fields_resolve : mixedEnv.structFields ⟨none,"Mixed"⟩ .storage =
    some [("delta",.int ⟨true,16,by decide,by decide,by decide⟩),
      ("recipient",.address true),("ready",.bool)] := rfl

theorem mixed_computed_fields :
    (produce "mixed-fields" mixedEnv .storage).isSome = true ∧
    targetFields mixedEnv .storage ⟨0,by decide⟩ =
      [("delta",.prim .int),("recipient",.prim .uint),("ready",.prim .bool)] := by decide

def unresolvedDecl : Source.Decl :=
  ⟨.struct,"Unresolved",none,true,
    .struct "Unresolved" (.structMember (.userType ⟨"Missing",[]⟩) "lost") .nil⟩
def unresolvedEnv : Source.Env := ⟨[unresolvedDecl]⟩

theorem unresolved_fields : unresolvedEnv.structFields ⟨none,"Unresolved"⟩ .memory = none := rfl

theorem unresolved_not_vacuously_admitted :
    (produce "failed-resolution" unresolvedEnv .memory).isNone = true := by decide

end Solidity.Lowering.V07.PrimitiveGraphControls
