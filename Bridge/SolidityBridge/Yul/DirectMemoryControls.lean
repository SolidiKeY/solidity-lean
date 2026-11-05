import SolidityBridge.Yul.DirectMemory
import Solidity.Yul.Compilation.PhysicalStoreControls
import Solidity.Backend.Environment.CompositionChecks

/-! Concrete direct-MSTORE/view/image/hash controls. The native host-sized
writer counterexample is not repaired or excluded by this local-model slice. -/
namespace SolidityBridge.Yul.DirectMemory.Controls
open Solidity
open Solidity.Yul.Views
open Solidity.Yul.Compilation
open Backend.Environment
abbrev dirty := PhysicalStore.Controls.dirty
abbrev payload := PhysicalStore.Controls.payload
abbrev memory := PhysicalStore.Controls.memory
abbrev initial := PhysicalStore.Controls.initial
abbrev image := PhysicalStore.Controls.image
abbrev imageInput := PhysicalStore.Controls.imageInput
open Solidity.Yul.Views.Controls (mixedPlacement mixedResidual)

theorem unaligned_refinement (tail : List Backend.Environment.Word) (m : ByteView) :
    runSlice sample (storeCode 31 payload) ⟨tail,m⟩ =
      runSlice sample (PhysicalStore.wordCode 31 payload) ⟨tail,m⟩ :=
  materialized_agreement sample 31 payload ⟨tail,m⟩ (by decide)

theorem unaligned_read :
    (runSlice sample (storeCode 31 payload) initial).map (fun out => mload out.memory 31) =
      some payload := view_read_after_store sample 31 payload initial

theorem typed_image_frame :
    image.Reads (mstore imageInput.memory 31 payload) (mixedPlacement.address 0) :=
  (image_preserved image sample initial.stack mixedResidual (mixedPlacement.address 0)
    31 payload (Or.inl (by decide))).2

def observe (code : Backend.Program) :=
  (runSlice sample code initial).map (fun out =>
    (out.stack.map (fun w => w.1.toNat), (mload out.memory 31).val,
      out.memory 30,out.memory 31,out.memory 62,out.memory 63))
#guard observe (storeCode 31 payload) = some ([77,99],payload.val,39,0xab,1,72)
#guard observe (storeCode 31 payload) =
  (runSlice sample (PhysicalStore.wordCode 31 payload) initial).map (fun out =>
    (out.stack.map (fun w => w.1.toNat), (mload out.memory 31).val,
      out.memory 30,out.memory 31,out.memory 62,out.memory 63))
#guard (runSlice sample (storeCode 31 0) initial).map (fun out => readBytes out.memory 31 32) =
  some (List.replicate 32 0)
#guard (runSlice sample (storeCode 31 ⟨2^256-1,by decide⟩) initial).map
  (fun out => readBytes out.memory 31 32) = some (List.replicate 32 255)
#check Backend.decode_encode (storeCode 31 payload)
#guard (Backend.encode (storeCode 31 payload)).getLast? = some 0x52
#guard (storeCode 31 payload).length = 3
#guard (PhysicalStore.wordCode 31 payload).length = 96
#guard (storeThenHash 31 payload).length = 6
#guard (PhysicalHash.storeThenHash 31 payload).length = 99
#guard (runSlice sample (storeThenHash 31 payload) initial).map
  (fun out => out.stack.map (fun w => w.1.toNat)) =
  some ((keccak256 Roadmap.Evm.withKeccak (mstore memory 31 payload) 31 32).val :: [77,99])
#guard (selectStore ⟨2^256-32,by decide⟩ payload).isSome
#guard (selectStore ⟨2^256-31,by decide⟩ payload).isNone
#guard (selectStore ⟨2^256-1,by decide⟩ payload).isNone
-- Do not add a host-size exclusion to hide the separately published native
-- writer mismatch. This proves only the existing Nat-map local semantics.
#guard (selectStore ⟨2^64,by decide⟩ dirty).isSome
#guard (runSlice sample (storeCode ⟨2^64,by decide⟩ dirty) initial).map
  (fun out => (out.memory 0,(mload out.memory (2^64)).val)) = some (9,dirty.val)
#guard (runSlice sample [.op .MSTORE] (⟨[],memory⟩ : Slice)).isNone
#guard (runSlice sample [.op .MSTORE] (⟨[PhysicalHash.targetWord 31],memory⟩ : Slice)).isNone
-- These operations remain unsupported by the unchanged target slice.
#guard (runSlice sample [.op .MLOAD] (⟨[PhysicalHash.targetWord 31],memory⟩ : Slice)).isNone
#guard (runSlice sample [.op .SSTORE] initial).isNone
-- Reversing operands writes at payload, so byte31 stays its original40.
#guard (runSlice sample [.op .MSTORE]
  (⟨PhysicalHash.targetWord payload :: PhysicalHash.targetWord 31 :: initial.stack,memory⟩ : Slice)).map
  (fun out => out.memory 31) = some 40
-- Dropping object disjointness changes the old image's length3 to1.
#guard (runSlice sample (storeCode 128 1) imageInput).map
  (fun out => (mload out.memory 128).val) = some 1
#guard (runSlice sample (storeCode 31 payload) imageInput).map
  (fun out => (mload out.memory 128).val) = some 3
-- Caller-preserving local success is not physical stack capacity.
def oversized : Slice := ⟨List.replicate 1025 (uintOfNat 1),memory⟩
#guard (runSlice sample (storeCode 31 dirty) oversized).map (fun out => out.stack.length) = some 1025

/-- All four actual instruction prefixes fit at the exact1022caller limit. -/
theorem prefix_room : ∀ k, k ≤ 3 →
    ∃ out, runSlice sample ((storeCode 31 dirty).take k)
      (⟨List.replicate 1022 (uintOfNat 1),memory⟩ : Slice) = some out ∧
      out.stack.length ≤ 1024 := by
  apply (capacity_iff sample 31 dirty _).mpr
  change (List.replicate 1022 (uintOfNat 1)).length+2≤1024
  rw [List.length_replicate]
  decide

/-- Numeric success at1023caller words cannot provide this prefix certificate. -/
theorem prefix_refused : ¬ (∀ k, k ≤ 3 →
    ∃ out, runSlice sample ((storeCode 31 dirty).take k)
      (⟨List.replicate 1023 (uintOfNat 1),memory⟩ : Slice) = some out ∧
      out.stack.length ≤ 1024) := by
  intro all
  have room := (capacity_iff sample 31 dirty
    (⟨List.replicate 1023 (uintOfNat 1),memory⟩ : Slice)).mp all
  change (List.replicate 1023 (uintOfNat 1)).length+2≤1024 at room
  rw [List.length_replicate] at room
  omega

/-- info: 'SolidityBridge.Yul.DirectMemory.Controls.unaligned_refinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unaligned_refinement
/-- info: 'SolidityBridge.Yul.DirectMemory.Controls.unaligned_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unaligned_read
/-- info: 'SolidityBridge.Yul.DirectMemory.Controls.typed_image_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms typed_image_frame
/-- info: 'SolidityBridge.Yul.DirectMemory.Controls.prefix_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_room
/-- info: 'SolidityBridge.Yul.DirectMemory.Controls.prefix_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_refused
end SolidityBridge.Yul.DirectMemory.Controls
