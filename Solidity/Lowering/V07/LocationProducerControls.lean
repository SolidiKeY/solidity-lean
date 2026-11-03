import Solidity.Lowering.V07.LocationGraphLaws
import Solidity.Lowering.V07.LocationGraphProducer
/-! H15 computed per-location producer controls. These observe actual Source
metadata and certificates, not external solc/EVM execution or Source admission. -/
namespace Solidity.Lowering.V07.LocationProducerControls
open Solidity Solidity.Lowering.V07
open LocationGraphProducer
abbrev mixed := LocationGraphLaws.mixed

theorem mixed_memory_success : (produce "h15-computed-memory" mixed .memory).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

theorem mixed_storage_success : (produce "h15-computed-storage" mixed .storage).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

theorem mixed_calldata_success : (produce "h15-computed-calldata" mixed .calldata).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

def memoryResult := (produce "h15-computed-memory" mixed .memory).get mixed_memory_success
def storageResult := (produce "h15-computed-storage" mixed .storage).get mixed_storage_success

theorem memory_physical_identity : (choices mixed .memory).length = 1 ∧
    memoryResult.1.declId ⟨0,by decide⟩ = 1 ∧
    (memoryResult.2.sourceIndex ⟨0,by decide⟩).val = 1 := by
  first | (simp only []; done) | decide | omega | rfl

theorem storage_physical_identities : (choices mixed .storage).length = 2 ∧
    storageResult.1.declId ⟨0,by decide⟩ = 0 ∧
    storageResult.1.declId ⟨1,by decide⟩ = 1 := by
  first | (simp only []; done) | decide | omega | rfl

theorem memory_typed_fields : memoryResult.1.fields ⟨0,by decide⟩ = [("value",.prim .uint)] := by
  first | (simp only []; done) | decide | omega | rfl

theorem storage_recursive_fields : storageResult.1.fields ⟨0,by decide⟩ =
    [("next",.mapping .uint (.node ⟨0,by decide⟩))] := by
  first | (simp only []; done) | decide | omega | rfl

theorem storage_only_has_empty_memory_view :
    (choices RecursiveGraphControls.mappingEnv .memory).length = 0 ∧
    (produce "empty-location-view-not-source-admission" RecursiveGraphControls.mappingEnv .memory).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

def chain : Source.Env := ⟨RecursiveGraphControls.mapDecl :: RecursiveGraphControls.chain.decls⟩

theorem chain_memory_success : (produce "inline-chain-after-location-selection" chain .memory).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

def chainResult := (produce "inline-chain-after-location-selection" chain .memory).get chain_memory_success

theorem chain_memory_ids_and_ranks :
    (choices chain .memory).length = 3 ∧
    chainResult.1.declId ⟨0,by decide⟩ = 2 ∧
    chainResult.1.declId ⟨1,by decide⟩ = 3 ∧
    chainResult.1.declId ⟨2,by decide⟩ = 4 ∧
    chainResult.1.rank ⟨0,by decide⟩ = 3 ∧
    chainResult.1.rank ⟨1,by decide⟩ = 2 ∧
    chainResult.1.rank ⟨2,by decide⟩ = 1 := by
  first | (simp only []; done) | decide | omega | rfl

theorem guarded_self_memory_success :
    (produce "guarded-self" GraphAdmissionBoundary.guardedEnv .memory).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

theorem inline_cycle_still_fails :
    (produce "no-inline-cycle" GraphAdmissionBoundary.directEnv .memory).isNone = true := by
  first | (simp only []; done) | decide | omega | rfl

theorem scoped_names_preserved :
    (produce "same-name-different-scope" PrimitiveGraphControls.scopedEnv .memory).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

def withBytes : Source.Env := ⟨[RecursiveGraphControls.mapDecl,LocationGraphLaws.plain,PrimitiveGraphControls.byteDecl]⟩

theorem unsupported_admissible_field_not_silently_omitted :
    (choices withBytes .memory).length = 2 ∧
    (produce "unsupported-field-not-filtered-out" withBytes .memory).isNone = true := by
  first | (simp only []; done) | decide | omega | rfl

theorem collapsed_identity_wrong : memoryResult.1.declId ⟨0,by decide⟩ ≠ 0 := by
  first | (simp only []; done) | decide | omega | rfl

def wrapperDecl : Source.Decl :=
  ⟨.struct,"Wrapper",none,true,.struct "Wrapper"
    (.structMember (.array (.array (.userType ⟨"Loop",[]⟩) .none) .none) "nested") .nil⟩
def transitiveEnv : Source.Env := ⟨[RecursiveGraphControls.mapDecl,wrapperDecl,LocationGraphLaws.plain]⟩

theorem transitive_memory_success : (produce "transitive-memory" transitiveEnv .memory).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

theorem transitive_storage_success : (produce "transitive-storage" transitiveEnv .storage).isSome = true := by
  first | (simp only []; done) | decide | omega | rfl

def transitiveMemoryResult := (produce "transitive-memory" transitiveEnv .memory).get transitive_memory_success
def transitiveStorageResult := (produce "transitive-storage" transitiveEnv .storage).get transitive_storage_success

theorem transitive_selection : (choices transitiveEnv .memory).length = 1 ∧
    transitiveMemoryResult.1.declId ⟨0,by decide⟩ = 2 ∧
    (choices transitiveEnv .storage).length = 3 ∧ transitiveStorageResult.1.declId ⟨1,by decide⟩ = 1 := by
  first | (simp only []; done) | decide | omega | rfl

theorem transitive_storage_fields : transitiveStorageResult.1.fields ⟨1,by decide⟩ =
    [("nested",.array (.array (.node ⟨0,by decide⟩)))] := by
  first | (simp only []; done) | decide | omega | rfl


end Solidity.Lowering.V07.LocationProducerControls
