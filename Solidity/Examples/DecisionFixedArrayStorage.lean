import Solidity.Calculus.DecisionFixedArrayStorage
import Solidity.Examples.DecisionFixedArrayPath

/-! # Inhabited storage-prefix observation controls
Actual map/nested storage roots, non-default sibling/root frames, absence and
missing-length countercontrols. The array decision gap pins are unchanged.
-/
namespace Solidity.Examples.DecisionFixedArrayStorage
open Solidity.Decide
set_option Elab.async false

def Store : Contract := contract!{
  mapping(uint => uint[3]) rows;
  uint[3][2] nested;
  uint sentinel;
}

private theorem rowsType : Store.rootType "rows" =
    some (.ref (.mapping .uint (.ref (.fixed (.prim .uint) 3)))) := by decide +kernel
private theorem nestedType : Store.rootType "nested" =
    some (.ref (.fixed (.ref (.fixed (.prim .uint) 3)) 2)) := by decide +kernel
private theorem sentinelType : Store.rootType "sentinel" = some (.prim .uint) := by decide +kernel

def original : Storage Store :=
  (((Storage.init Store).set rowsType DecisionFixedArrayPath.mapping).set
    nestedType DecisionFixedArrayPath.nested).set sentinelType (.prim (uintOfNat 42))

def keyResult : Option (Storage Store) :=
  fixedFloorStorageAtPath rowsType DecisionFixedArrayPath.keyPrefix [2, 3] original

def nestedResult : Option (Storage Store) :=
  fixedFloorStorageAtPath nestedType DecisionFixedArrayPath.arrayPrefix [2, 3] original

/-- The selected row changes while another non-default mapping key is framed. -/
theorem mapping_word_controls :
    keyResult.map (fun st => st.obs.word
      (.ref ⟨"rows", rowsType, .key (uintOfNat 5) (.atF (uintOfNat 1) .nil)⟩)) =
        some (uintOfNat 7) ∧
    original.obs.word (.ref ⟨"rows", rowsType, .key (uintOfNat 5) (.atF (uintOfNat 1) .nil)⟩) =
      uintOfNat 9 ∧
    keyResult.map (fun st => st.obs.word
      (.ref ⟨"rows", rowsType, .key (uintOfNat 6) (.atF (uintOfNat 1) .nil)⟩)) =
        some (uintOfNat 9) := by decide +kernel

/-- Actual successful/out-of-range presence observations are distinguished. -/
theorem mapping_presence_controls :
    keyResult.map (fun st => st.obs.has
      (.ref ⟨"rows", rowsType, .key (uintOfNat 5) (.atF (uintOfNat 2) .nil)⟩)) = some true ∧
    keyResult.map (fun st => st.obs.has
      (.ref ⟨"rows", rowsType, .key (uintOfNat 5) (.atF (uintOfNat 3) .nil)⟩)) = some false := by
  decide +kernel

/-- Another root contains a non-default sentinel, preserved as a complete value. -/
theorem other_root_frame {st' : Storage Store} (hs : keyResult = some st') :
    st'.get sentinelType = original.get sentinelType :=
  fixedFloorStorageAtPath_other_root rowsType DecisionFixedArrayPath.keyPrefix
    [2, 3] original hs sentinelType (by decide)

theorem nested_word_controls :
    nestedResult.map (fun st => st.obs.word
      (.ref ⟨"nested", nestedType, .atF (uintOfNat 1) (.atF (uintOfNat 1) .nil)⟩)) =
        some (uintOfNat 7) ∧
    nestedResult.map (fun st => st.obs.word
      (.ref ⟨"sentinel", sentinelType, .nil⟩)) = some (uintOfNat 42) := by decide +kernel

/-- An absent outer prefix does not install an enclosing default object. -/
theorem absent_prefix : (fixedFloorStorageAtPath nestedType
    (.atF (uintOfNat 2) .nil) [2, 3] original).isNone = true := by decide +kernel

/-- Omitting the length breakpoint would give a false presence transport claim. -/
theorem length_premise_necessary :
    (fixedFloorStorageAtPath rowsType DecisionFixedArrayPath.keyPrefix [] original).map
      (fun st => st.obs.has (.ref ⟨"rows", rowsType,
        .key (uintOfNat 5) (.atF (uintOfNat 3) .nil)⟩)) = some false ∧
    original.obs.has (.ref ⟨"rows", rowsType,
      .key (uintOfNat 5) (.atF (fixedFloorIndex [] (uintOfNat 3)) .nil)⟩) = true := by
  decide +kernel

end Solidity.Examples.DecisionFixedArrayStorage
