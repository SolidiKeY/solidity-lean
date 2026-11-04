import Solidity.Yul.Compilation.PhysicalHash

/-! Direct MSTORE compilation against the actual byte-addressed local target
and VY2 view. No replacement memory/word/layout semantics. This does not assert
pinned native ByteArray correctness, gas/host bounds, MemOK or G24 writeback. -/
namespace SolidityBridge.Yul.DirectMemory
open Solidity
open Solidity.Yul.Views
open Solidity.Yul.Compilation
open Backend.Environment

/-- The target ABI encoder and producer bytes agree at every byte position. -/
theorem bytes_agree (value : Roadmap.Word) :
    Semantics.wordBytes value.val = PhysicalStore.bytesOf value := by
  apply List.ext_getElem
  · simp only [Semantics.wordBytes,List.length_map,List.length_range,
      PhysicalStore.bytesOf,List.length_ofFn]
  · intro i left right
    simp only [Semantics.wordBytes,PhysicalStore.bytesOf,List.getElem_map,
      List.getElem_range,List.getElem_ofFn,wordByte,Nat.toUInt8_eq]
    exact UInt8.ofNat_mod_size

/-- Actual operand order: address on top, full dirty value immediately below. -/
theorem opcode_run (f : Frame) (address value : Roadmap.Word)
    (tail : List Backend.Environment.Word) (memory : ByteView) :
    runSlice f [.op .MSTORE]
      ⟨PhysicalHash.targetWord address :: PhysicalHash.targetWord value :: tail,memory⟩ =
      some ⟨tail,mstore memory address.val value⟩ := by
  change some (⟨tail,writeBytes memory address.val (Semantics.wordBytes value.val)⟩ : Slice) = _
  rw [bytes_agree,PhysicalStore.word_memory]

/-- Three real instructions, with the value pushed before the address. -/
def storeCode (address value : Roadmap.Word) : Backend.Program :=
  [push256 value,push256 address,.op .MSTORE]

def selectStore (address value : Roadmap.Word) : Option Backend.Program :=
  if address.val+32≤2^256 then some (storeCode address value) else none

/-- Exact local target memory update for arbitrary caller and initial bytes.
The unbounded Nat byte map here is not the pinned native host writer. -/
theorem store_run (f : Frame) (address value : Roadmap.Word) (s : Slice) :
    runSlice f (storeCode address value) s =
      some {s with memory := mstore s.memory address.val value} := by
  rw [runSlice_crypto f _ _ (by rfl)]
  simp only [storeCode,push256,runCrypto,cryptoStep_constant,Option.bind_some]
  change some (⟨s.stack,writeBytes s.memory address.val (Semantics.wordBytes value.val)⟩ : Slice) = _
  rw [bytes_agree,PhysicalStore.word_memory]

/-- Actual single PUSH execution in the same local memory target. -/
theorem push_run (f : Frame) (value : Roadmap.Word) (s : Slice) :
    runSlice f [push256 value] s =
      some {s with stack := PhysicalHash.targetWord value :: s.stack} := by
  rw [runSlice_crypto f _ _ (by rfl)]
  simp only [push256,runCrypto,cryptoStep_constant,Option.bind_some]
  rfl

/-- The real two-word peak immediately before MSTORE. -/
theorem operand_prefix_run (f : Frame) (address value : Roadmap.Word) (s : Slice) :
    runSlice f [push256 value,push256 address] s =
      some {s with stack := PhysicalHash.targetWord address :: PhysicalHash.targetWord value :: s.stack} := by
  change runSlice f ([push256 value] ++ [push256 address]) s = _
  rw [runSlice_append,push_run,Option.bind_some,push_run]

/-- Necessary and sufficient room for EVERY actual local execution prefix.
This is not Scalar.stackBound (Scalar.run refuses MSTORE), nor native gas or
host-writer adequacy. No desired prefix execution is an input assumption. -/
theorem capacity_iff (f : Frame) (address value : Roadmap.Word) (s : Slice) :
    (∀ k, k ≤ (storeCode address value).length →
      ∃ out, runSlice f ((storeCode address value).take k) s = some out ∧
        out.stack.length ≤ 1024) ↔ s.stack.length+2≤1024 := by
  constructor
  · intro all
    obtain ⟨out,ran,room⟩ := all 2 (by change 2≤3; decide)
    change runSlice f [push256 value,push256 address] s = some out at ran
    rw [operand_prefix_run] at ran
    cases ran
    exact room
  · intro room k bound
    change k≤3 at bound
    cases k with
    | zero => exact ⟨s,rfl,by omega⟩
    | succ k =>
      cases k with
      | zero =>
        exact ⟨{s with stack := PhysicalHash.targetWord value :: s.stack},push_run f value s,by
          change s.stack.length+1≤1024
          omega⟩
      | succ k =>
        cases k with
        | zero =>
          exact ⟨{s with stack := PhysicalHash.targetWord address :: PhysicalHash.targetWord value :: s.stack},
            operand_prefix_run f address value s,room⟩
        | succ k =>
          have zero : k = 0 := by omega
          subst k
          exact ⟨{s with memory := mstore s.memory address.val value},store_run f address value s,by
            change s.stack.length≤1024
            omega⟩

/-- Exact compiler-slice refinement of the previously published32byte stores.
The existing materializer's no-wrap premise is retained, not assumed away. -/
theorem materialized_agreement (f : Frame) (address value : Roadmap.Word) (s : Slice)
    (fits : address.val+32≤2^256) :
    runSlice f (storeCode address value) s =
      runSlice f (PhysicalStore.wordCode address.val value) s := by
  rw [store_run,PhysicalStore.wordCode,runSlice_data f _ _ (materialize_supported _ _)]
  rw [materialize_correct]
  · rw [PhysicalStore.word_memory]
  · simpa only [PhysicalStore.bytesOf,List.length_ofFn] using fits

/-- A successful compiler selection retains the same old no-wrap domain. -/
theorem selected_agreement (f : Frame) (address value : Roadmap.Word) (s : Slice)
    (code : Backend.Program) (selected : selectStore address value = some code) :
    address.val+32≤2^256 ∧
      runSlice f code s = runSlice f (PhysicalStore.wordCode address.val value) s := by
  unfold selectStore at selected
  split at selected
  next fits =>
    cases selected
    exact ⟨fits,materialized_agreement f address value s fits⟩
  next no => cases selected

/-- This is a source-view read after an actual target store, NOT a target
MLOAD execution theorem (the local target refuses MLOAD). -/
theorem view_read_after_store (f : Frame) (address value : Roadmap.Word) (s : Slice) :
    (runSlice f (storeCode address value) s).map (fun out => mload out.memory address.val) =
      some value := by
  rw [store_run]
  change some (mload (mstore s.memory address.val value) address.val) = some value
  rw [mload_mstore]

/-- Whole-word disjointness preserves the actual intrinsic object image.
This frames one supplied image, not every object, ownership or global MemOK. -/
theorem image_preserved {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (f : Frame) (tail : List Backend.Environment.Word) (m : ByteView) (base : Nat)
    (address value : Roadmap.Word)
    (outside : address.val+32≤base ∨ base+image.span≤address.val) :
    runSlice f (storeCode address value) ⟨tail,image.encode m base⟩ =
      some ⟨tail,mstore (image.encode m base) address.val value⟩ ∧
    image.Reads (mstore (image.encode m base) address.val value) base := by
  constructor
  · exact store_run f address value ⟨tail,image.encode m base⟩
  · apply image.reads_congr _ (image.encode m base) base
    · intro i inside
      exact mstore_outside (image.encode m base) address.val (base+i) value (by omega)
    · exact image.encode_reads m base

/-- Direct store followed by the unchanged canonical source hash slice. -/
def storeThenHash (address value : Roadmap.Word) : Backend.Program :=
  storeCode address value ++ PhysicalHash.hashCode address 32

theorem store_hash_run (f : Frame) (address value : Roadmap.Word) (s : Slice) :
    runSlice f (storeThenHash address value) s =
      some {s with
        memory := mstore s.memory address.val value
        stack := PhysicalHash.targetWord (keccak256 Roadmap.Evm.withKeccak
          (mstore s.memory address.val value) address.val 32) :: s.stack} := by
  rw [storeThenHash,runSlice_append,store_run,Option.bind_some]
  rw [PhysicalHash.hashCode,runSlice_crypto f _ _ (keccak_supported address 32),keccak_correct]
  rw [PhysicalHash.digest_view]
  rfl

/-- info: 'SolidityBridge.Yul.DirectMemory.bytes_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bytes_agree
/-- info: 'SolidityBridge.Yul.DirectMemory.opcode_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms opcode_run
/-- info: 'SolidityBridge.Yul.DirectMemory.store_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms store_run
/-- info: 'SolidityBridge.Yul.DirectMemory.materialized_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms materialized_agreement
/-- info: 'SolidityBridge.Yul.DirectMemory.store_hash_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms store_hash_run
/-- info: 'SolidityBridge.Yul.DirectMemory.selected_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selected_agreement
/-- info: 'SolidityBridge.Yul.DirectMemory.view_read_after_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms view_read_after_store
/-- info: 'SolidityBridge.Yul.DirectMemory.image_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms image_preserved
/-- info: 'SolidityBridge.Yul.DirectMemory.push_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms push_run
/-- info: 'SolidityBridge.Yul.DirectMemory.operand_prefix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms operand_prefix_run
/-- info: 'SolidityBridge.Yul.DirectMemory.capacity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms capacity_iff
end SolidityBridge.Yul.DirectMemory
