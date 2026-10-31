import Solidity.Yul.Views.MemoryContract
import Solidity.Yul.Views.Controls

/-! Inhabited nondeterministic layout and reserved-area controls. -/
namespace Solidity.Yul.Views.Controls

def twoObjects : Source.Heap layout where
  cells a := if a < 2 then some ⟨.bytes .memory, .bytes [0xaa]⟩ else none
  next := 2
  bounded a h := by simp only [show ¬ a < 2 by omega, if_false]

/-- Valid base choices for the same two typed logical objects. -/
def placementShift (gap : Fin 65) : Placement twoObjects where
  address a := 128 + gap.val + a * 64
  shape _ := .bytes 1
  free := ⟨256 + gap.val, by have h := gap.isLt; omega⟩
  free_start := by change 128 ≤ 256 + gap.val; omega
  distinct a b _ _ h := by omega
  typed a τ d h := by
    by_cases ha : a < 2
    · simp only [twoObjects, ha, if_true] at h
      cases Option.some.inj h
      exact .bytes _
    · simp only [twoObjects, ha, if_false] at h
      contradiction
  starts a _ := by omega
  ends a h := by
    have ha : a < 2 := by
      by_cases hn : a < 2
      · exact hn
      · simp only [twoObjects, hn, if_false, Option.isSome_none, Bool.false_eq_true] at h
    change 128 + gap.val + a * 64 + 64 ≤ 256 + gap.val
    omega
  separate a b _ _ h := by
    change 128 + gap.val + a * 64 + 64 ≤ 128 + gap.val + b * 64 ∨
      128 + gap.val + b * 64 + 64 ≤ 128 + gap.val + a * 64
    omega

def placement (gap : Fin 3) : Placement twoObjects :=
  placementShift ⟨gap.val * 32, by have h := gap.isLt; omega⟩

theorem unaligned_allocation : (placementShift 1).address 0 = 129 ∧
    (placementShift 1).free.val = 257 := by decide

theorem allocation_choices : (placement 0).address 0 = 128 ∧ (placement 1).address 0 = 160 ∧
    (placement 0).address 0 ≠ (placement 1).address 0 := by decide

theorem distinct_objects : (placement 0).address 0 ≠ (placement 0).address 1 := by decide

theorem low_free_pointer_refused (p : Placement (Source.Heap.empty (D := layout))) : p.free.val ≠ 0 := by
  have h := p.free_start
  omega

def reserved : ByteView := mstore zero 64 ⟨128, by decide⟩

theorem reserved_witness : ReservedOK reserved ⟨128, by decide⟩ := by
  constructor
  · exact congrArg Fin.val (mload_mstore zero 64 ⟨128, by decide⟩)
  · intro i
    apply mstore_outside
    omega

theorem shapes : MemoryShape.size (.bytes 33) = 96 ∧ MemoryShape.size (.array true 3) = 128 ∧
    MemoryShape.size (.array false 3) = 96 ∧ MemoryShape.size (.strct 3) = 96 := by decide

def environment : Environment where
  coinbase := ⟨0x1234, by decide⟩
  origin := ⟨0x5678, by decide⟩
  number := 1000
  timestamp := 9999
  prevrandao := 7
  gaslimit := 30000000
  chainid := 1
  basefee := 10
  blobbasefee := 11
  gasprice := 12
  historicalHash _ := 42
  blobHashes := [55]

theorem environment_vectors : environment.read .number = 1000 ∧
    environment.read .timestamp = 9999 ∧ blockhash environment 744 = 42 ∧
    blockhash environment 743 = 0 ∧ blockhash environment 1000 = 0 ∧
    blobhash environment 0 = 55 ∧ blobhash environment 1 = 0 := by decide

#print axioms placement
#print axioms reserved_witness
#print axioms Field.save_lt
#print axioms environment_address_width

end Solidity.Yul.Views.Controls
