import Solidity.Backend.Aggregates.G18Graph
import Solidity.Lowering.V07.GraphIdentityControls

/-! Extend the producer's REAL Cell declaration with a real storage variable.
This inhabits graph_storage_path's starting admission; no source/IR execution
or blanket accepted-source graph extraction is inferred. -/
namespace Solidity.Backend.Aggregates.GraphRootControls
open Lowering.V07
open Lowering.V07.GraphControls (cellDecl cellName schema)

def rootDecl : Source.Decl :=
  ⟨.stateVar, "root", none, true,
    .stateVar (.userType ⟨"Cell", []⟩) none none none false "root" .none⟩

def env : Source.Env := ⟨[cellDecl, rootDecl]⟩

def graph : DeclarationGraph env .storage schema where
  sourceName := fun _ => cellName
  sourceName_injective := by intro i j _; apply Fin.ext; omega
  sourceIndex := fun _ => ⟨0, by decide⟩
  identity := fun _ => rfl
  source_kind := fun _ => rfl
  source_scope := fun _ => rfl
  source_name := fun _ => rfl
  source_resolves := fun _ => rfl
  target_name := fun _ => rfl
  sourceFields := fun _ => [("value", .int .u8)]
  fields_resolve := fun _ => rfl
  fields_relate := fun _ => .cons rfl (.int .u8) .nil
  complete := by
    rintro ⟨j, hj⟩ hk
    match j with
    | 0 => exact ⟨⟨0, by decide⟩, rfl⟩
    | 1 => cases hk
    | j+2 => change j+2 < 2 at hj; omega

def root : Source.SPath := ⟨⟨none, "root"⟩, []⟩

theorem admitted_root : env.pathTy root = some (.struct .storage cellName) := rfl

/-- NEW graph_storage_path applied with an actual resolved root, not a supplied
future admission theorem. The complete declaration certificate is inhabited. -/
theorem selected_field :
    ∃ τ, env.pathTy {root with steps := root.steps ++ [.field 0]} = some τ ∧
      GraphTypeRel env.layout graph.sourceName τ (.prim .uint) :=
  graph_storage_path graph ⟨0, by decide⟩ root admitted_root 0 "value" (.prim .uint) rfl

theorem exact_selected_type :
    env.pathTy {root with steps := root.steps ++ [.field 0]} = some (.int .u8) := rfl

theorem wrong_field_index :
    env.pathTy {root with steps := root.steps ++ [.field 1]} = none := rfl

theorem wrong_key_step :
    env.pathTy {root with steps := root.steps ++ [.key [0]]} = none := rfl

theorem wrong_root : env.pathTy ⟨⟨none, "missing"⟩, []⟩ = none := rfl

#print axioms selected_field
#print axioms exact_selected_type
#print axioms wrong_field_index
end Solidity.Backend.Aggregates.GraphRootControls

namespace Solidity.Backend.Aggregates
open Lowering.V07

namespace GraphClients
open Lowering.V07.GraphControls

theorem storage_field :
    ∃ τ, env.fieldTy? cellName .storage 0 = some τ ∧
      ((certificate .storage).sourceFields ⟨0, by decide⟩)[0]? = some ("value", τ) ∧
      GraphTypeRel env.layout (certificate .storage).sourceName τ (.prim .uint) :=
  graph_field_type (certificate .storage) ⟨0, by decide⟩ 0 "value" (.prim .uint) rfl

theorem memory_field :
    ∃ τ, (env.layout.fields cellName)[0]? = some τ ∧
      GraphTypeRel env.layout (certificate .memory).sourceName τ (.prim .uint) :=
  graph_memory_field (certificate .memory) ⟨0, by decide⟩ 0 "value" (.prim .uint) rfl

/-- Direct wrong-type candidate for the new field consumer's conclusion. -/
theorem wrong_type : ¬ ∃ τ, env.fieldTy? cellName .storage 0 = some τ ∧
    GraphTypeRel env.layout (certificate .storage).sourceName τ (.prim .bool) := by
  rintro ⟨τ, ht, hr⟩
  have he : Source.STy.int .u8 = τ := Option.some.inj ht
  subst τ
  cases hr

theorem wrong_field_position : (schema.fields ⟨0, by decide⟩)[1]? ≠
    some ("value", .prim .uint) := by decide

end GraphClients

#print axioms GraphClients.storage_field
#print axioms GraphClients.memory_field
#print axioms GraphClients.wrong_type
end Solidity.Backend.Aggregates
