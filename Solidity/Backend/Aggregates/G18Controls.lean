import Solidity.Backend.Aggregates.G18Storage
import Solidity.Backend.Aggregates.G18Memory
import Solidity.Source.StateExamples

/-! Concrete checks of actual source definitions. These do not instantiate all
premises of nested_write_observe (G18MemoryClient does) and do not apply
`path_append`/`array_path`/`mapping_path`. -/
namespace Solidity.Backend.Aggregates.Controls
open Source
open Source.StateExamples

def emptyEnv : Source.Env := ⟨[]⟩

theorem fixed_type_not_bound :
    emptyEnv.stepTy (.array .storage .bool (some 2)) (.index 99) = some .bool := rfl

theorem dynamic_index :
    emptyEnv.stepTy (.array .storage .bool none) (.index 1) = some .bool := rfl

theorem mapping_key :
    emptyEnv.stepTy (.mapping .bool (.array .storage .bool none)) (.key [0, 7]) =
      some (.array .storage .bool none) := rfl

theorem wrong_mapping_index :
    emptyEnv.stepTy (.mapping .bool .bool) (.index 0) = none := rfl

theorem wrong_array_key :
    emptyEnv.stepTy (.array .storage .bool none) (.key [0]) = none := rfl

theorem wrong_scalar_field : emptyEnv.stepTy .bool (.field 0) = none := rfl

theorem key_then_index :
    ([Source.Step.key [0,7], .index 1]).foldl
      (fun o s => o.bind (emptyEnv.stepTy · s))
      (some (.mapping .bool (.array .storage .bool none))) = some .bool := rfl

theorem wrong_order :
    ([Source.Step.index 1, .key [0,7]]).foldl
      (fun o s => o.bind (emptyEnv.stepTy · s))
      (some (.mapping .bool (.array .storage .bool none))) = none := rfl

/-- Actual nested source heap: writing the old child preserves the parent;
a subsequent allocation is fresh and preserves BOTH occupied cells. -/
theorem source_update_then_allocate :
    let written := heap.write 0 (single eight) rfl
    let grown := written.alloc ⟨arrTy, single seven⟩
    written.get 0 = some ⟨arrTy, single eight⟩ ∧
      written.get 1 = heap.get 1 ∧
      grown.2 = 2 ∧ grown.1.get 0 = written.get 0 ∧
      grown.1.get 1 = written.get 1 ∧
      grown.1.get 2 = some ⟨arrTy, single seven⟩ := by
  exact ⟨alias_seen.1, alias_seen.2, rfl,
    Heap.alloc_other _ _ (by decide), Heap.alloc_other _ _ (by decide), Heap.alloc_get _ _⟩

theorem source_wrong_next :
    (heap.write 0 (single eight) rfl).next ≠ 1 := by decide

#print axioms source_update_then_allocate
#print axioms wrong_order
end Solidity.Backend.Aggregates.Controls
