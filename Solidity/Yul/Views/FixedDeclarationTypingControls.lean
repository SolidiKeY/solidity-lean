import Solidity.Yul.Views.FixedDeclarationTyping
import Solidity.Yul.Views.FixedDeclarationFinal

namespace Solidity.Yul.Views.Controls

theorem recursive_all_paths_metadata_typed (c : ScalarPath recursiveDeclEnv.layout (recursiveDeclEnv.lay account))
    (member : c ∈ recursiveChecked.registrations) : (recursiveDeclEnv.pathTy c.path).isSome :=
  recursiveChecked.paths_typed c member

theorem recursive_actual_nested_types :
    recursiveDeclEnv.pathTy (recursiveGridPath 1 1 0) = some .bool ∧
    recursiveDeclEnv.pathTy (recursiveGridPath 1 1 1) = some (.int unsigned16) ∧
    recursiveDeclEnv.pathTy (recursiveValuePath 2) = some (.int recursiveUnsigned128) := ⟨rfl,rfl,rfl⟩

/-- The owner deliberately leaves index bounds to execution, while the derived
registry enumerates only actual fixed-count members. Both facts are retained. -/
theorem recursive_structural_index_boundary :
    recursiveDeclEnv.pathTy (recursiveGridPath 2 0 0) = some .bool ∧
    recursiveGridPath 2 0 0 ∉ (recursiveRegistry account).map ScalarPath.path :=
  ⟨rfl,recursive_out_of_range_not_registered⟩

def recursiveMissingField : Source.SPath := ⟨recursiveRoot,[.field 0,.index 0,.index 0,.field 2]⟩

theorem recursive_missing_metadata_fallback :
    recursiveDeclEnv.pathTy recursiveMissingField = none ∧
    recursiveDeclEnv.cellTy recursiveMissingField = .tuple [] ∧
    packDeclarationPaths recursiveDeclEnv (fun _ => recursiveMissingField) account 0 [("",.bool)] (8*32) = .error .cellMismatch :=
  ⟨rfl,rfl,rfl⟩

theorem recursive_wrong_root_type :
    (checkFixedDeclaration (FixedDeclaration.scalar (E := recursiveDeclEnv) .bool (by decide))
      recursiveRoot account 8).toOption.isNone := by decide

end Solidity.Yul.Views.Controls
