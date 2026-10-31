import Solidity.Yul.Views.HeapByteComposition

/-! Actual allocated source objects, aliases and the real owner MemOK. Ordinary
empty objects are not shared zero-slot references. No full assembly claim. -/
namespace Solidity.Yul.Views.Controls

def heapByteEnv : Source.Env := ⟨[]⟩
def byteOld : List UInt8 := [0x11, 0x22, 0x33]
def byteNew : List UInt8 := [0x99, 0x88, 0x77]
def stringOld : List UInt8 := List.replicate 33 0x61
def stringNew : List UInt8 := 0xff :: List.replicate 32 0x62
def byteOther : List UInt8 := [0xee, 0xdd, 0xcc]
def byteHeap : Source.Heap heapByteEnv.layout :=
  ((((Source.Heap.empty.alloc ⟨.bytes .memory, .bytes byteOld⟩).1).alloc
    ⟨.string .memory, .string stringOld⟩).1.alloc ⟨.bytes .memory, .bytes byteOther⟩).1

theorem byteHeap_present_lt (a : Nat) (h : (byteHeap.cells a).isSome) : a < 3 := by
  apply Nat.lt_of_not_le
  intro hn
  have hb := byteHeap.bounded a (by change 3 ≤ a; omega)
  rw [hb] at h
  cases h

def byteHeapShape (a : Nat) : MemoryShape := if a = 1 then .bytes 33 else .bytes 3

def bytePlacement (shift : Fin 33) : Placement byteHeap where
  address a := 128 + shift.val + a * 128
  shape := byteHeapShape
  free := ⟨512 + shift.val, by have hs := shift.isLt; omega⟩
  free_start := by change 128 ≤ 512 + shift.val; omega
  distinct a b _ _ h := by omega
  typed a τ d h := by
    change byteHeap.get a = some ⟨τ, d⟩ at h
    cases a with
    | zero =>
      change some (⟨.bytes .memory, Source.Data.bytes byteOld⟩ : Σ σ, Source.Data heapByteEnv.layout σ) = some ⟨τ, d⟩ at h
      cases h
      exact .bytes _
    | succ a =>
      cases a with
      | zero =>
        change some (⟨.string .memory, Source.Data.string stringOld⟩ : Σ σ, Source.Data heapByteEnv.layout σ) = some ⟨τ, d⟩ at h
        cases h
        exact .string _
      | succ a =>
        cases a with
        | zero =>
          change some (⟨.bytes .memory, Source.Data.bytes byteOther⟩ : Σ σ, Source.Data heapByteEnv.layout σ) = some ⟨τ, d⟩ at h
          cases h
          exact .bytes _
        | succ a =>
          have hb := byteHeap.bounded (a + 3) (by change 3 ≤ a + 3; omega)
          change byteHeap.cells (a + 3) = some ⟨τ, d⟩ at h
          rw [hb] at h
          cases h
  starts a _ := by omega
  ends a h := by
    have ha := byteHeap_present_lt a h
    by_cases he : a = 1
    · subst a; change 128 + shift.val + 128 + 96 ≤ 512 + shift.val; omega
    · change 128 + shift.val + a * 128 + (byteHeapShape a).size ≤ 512 + shift.val
      simp only [byteHeapShape, if_neg he]
      change 128 + shift.val + a * 128 + 64 ≤ 512 + shift.val
      omega
  separate a b _ _ h := by
    have small (a : Nat) : (byteHeapShape a).size ≤ 128 := by
      unfold byteHeapShape
      split <;> decide
    have ha := small a
    have hb := small b
    change 128 + shift.val + a * 128 + (byteHeapShape a).size ≤ 128 + shift.val + b * 128 ∨
      128 + shift.val + b * 128 + (byteHeapShape b).size ≤ 128 + shift.val + a * 128
    omega

def heapByteResidual : ByteView := mstore (mstore (fun _ => 0xa5) 64 512) 96 0

def beforeBytePhysical := bytesObjectView stringOld (by decide) (bytesObjectView byteOther (by decide) heapByteResidual 384) 256
def bytePhysical : ByteView := bytesObjectView byteOld (by decide) beforeBytePhysical 128
def byteChangedPhysical := bytesObjectView byteNew (by decide) bytePhysical 128
def bothChangedPhysical := bytesObjectView stringNew (by decide) byteChangedPhysical 256

def heapByteAfter := byteHeap.write 0 (Source.Data.bytes byteNew) (by rfl)
def heapStringAfter := byteHeap.write 1 (Source.Data.string stringNew) (by rfl)
def bothHeapAfter := heapByteAfter.write 1 (Source.Data.string stringNew) (by rfl)
def afterBytePlacement : Placement heapByteAfter :=
  heapWritePlacement byteHeap (bytePlacement 0) 0 (.bytes byteNew) (by rfl) (.bytes _)

theorem byte_changed : heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl byteChangedPhysical = some heapByteAfter :=
  heapByteWriteback_encode byteHeap (bytePlacement 0) 0 false byteOld byteNew rfl (by decide) rfl bytePhysical

theorem string_changed : heapByteWriteback heapByteAfter afterBytePlacement 1 true stringOld rfl bothChangedPhysical = some bothHeapAfter :=
  heapByteWriteback_encode heapByteAfter afterBytePlacement 1 true stringOld stringNew rfl (by decide) rfl byteChangedPhysical

theorem byte_unchanged_whole_heap : heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical = some byteHeap :=
  heapByteWriteback_unchanged byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical
    (congrArg Fin.val (bytesObject_header byteOld (by decide) beforeBytePhysical 128))
    (bytesObject_payload_list byteOld (by decide) beforeBytePhysical 128)

theorem string_unchanged_whole_heap : heapByteWriteback byteHeap (bytePlacement 0) 1 true stringOld rfl bytePhysical = some byteHeap :=
by
  have hb : (mload beforeBytePhysical 256).val = stringOld.length :=
    congrArg Fin.val (bytesObject_header stringOld (by decide) _ 256)
  have frame := bytesObject_other_object byteHeap (bytePlacement 0) 0 1 false true byteOld stringOld byteOld
    rfl rfl (by decide) (by decide) rfl beforeBytePhysical hb
  apply heapByteWriteback_unchanged byteHeap (bytePlacement 0) 1 true stringOld rfl bytePhysical
  · exact (congrArg Fin.val frame.1).trans hb
  · exact frame.2.1.trans (bytesObject_payload_list stringOld (by decide) _ 256)

theorem two_object_reverse_agreement : bothHeapAfter =
    heapStringAfter.write 0 (.bytes byteNew) (by rfl) :=
  heap_writes_commute byteHeap 0 1 (.bytes byteNew) (.string stringNew) rfl rfl (by decide)

def reverseStringPhysical := bytesObjectView stringNew (by decide) bytePhysical 256
def reverseBothPhysical := bytesObjectView byteNew (by decide) reverseStringPhysical 128
def afterStringPlacement : Placement heapStringAfter :=
  heapWritePlacement byteHeap (bytePlacement 0) 1 (.string stringNew) (by rfl) (.string _)

theorem reverse_string_writeback : heapByteWriteback byteHeap (bytePlacement 0) 1 true stringOld rfl reverseStringPhysical = some heapStringAfter :=
  heapByteWriteback_encode byteHeap (bytePlacement 0) 1 true stringOld stringNew rfl (by decide) rfl bytePhysical

theorem reverse_byte_writeback : heapByteWriteback heapStringAfter afterStringPlacement 0 false byteOld rfl reverseBothPhysical = some bothHeapAfter := by
  rw [two_object_reverse_agreement]
  exact heapByteWriteback_encode heapStringAfter afterStringPlacement 0 false byteOld byteNew rfl (by decide) rfl reverseStringPhysical

theorem other_cell_and_types_next : bothHeapAfter.get 2 = byteHeap.get 2 ∧ bothHeapAfter.ty = byteHeap.ty ∧
    bothHeapAfter.next = 3 ∧ bothHeapAfter.get 3 = none := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  funext a
  exact (Source.Heap.write_ty _ 1 a _ _).trans (Source.Heap.write_ty _ 0 a _ _)

def bytesAlias : Source.Val heapByteEnv.layout (.bytes .memory) := .memRef rfl 0
def stringAlias : Source.Val heapByteEnv.layout (.string .memory) := .memRef rfl 0

theorem actual_alias_observation : bytesAlias = .memRef rfl 0 ∧ stringAlias = .memRef rfl 0 ∧
    bothHeapAfter.get 0 = some ⟨.bytes .memory, .bytes byteNew⟩ ∧
    bothHeapAfter.get 1 = some ⟨.string .memory, .string stringNew⟩ := ⟨rfl, rfl, rfl, rfl⟩

def badHeaderPhysical := mstore byteChangedPhysical 128 4

theorem bad_header_no_preparation : heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl badHeaderPhysical = none := rfl

theorem wrong_declared_type : byteHeap.ty 0 ≠ some (.string .memory) := by decide
theorem unallocated_object : byteHeap.get 3 = none := rfl

theorem reserved_before : ReservedOK heapByteResidual 512 := by
  refine ⟨?_, ?_⟩
  · change (mload heapByteResidual 64).val = 512
    rw [show mload heapByteResidual 64 = mload (mstore (fun _ => 0xa5) 64 512) 64 from
      mload_congr _ _ 64 (fun i => mstore_outside _ 96 _ 0 (by have hi := i.isLt; omega)), mload_mstore]
    rfl
  · intro i
    have hz : wordByte (0 : Roadmap.Word) i = 0 := by
      change UInt8.ofNat ((0 : Roadmap.Word).val / 256 ^ (31 - i.val)) = 0
      rw [show (0 : Roadmap.Word).val = 0 by decide, Nat.zero_div]
      rfl
    exact (find_mstore _ 96 0 i).trans hz

theorem reserved_all_updates : ReservedOK bothChangedPhysical 512 := by
  apply bytesObject_reserved _ _ _ 256 _ (by decide)
  apply bytesObject_reserved _ _ _ 128 _ (by decide)
  apply bytesObject_reserved _ _ _ 128 _ (by decide)
  apply bytesObject_reserved _ _ _ 256 _ (by decide)
  exact bytesObject_reserved _ _ _ 384 _ (by decide) reserved_before

theorem physical_payload_padding : bothChangedPhysical 160 = 0x99 ∧ bothChangedPhysical 162 = 0x77 ∧
    bothChangedPhysical 163 = 0xa5 ∧ bothChangedPhysical 288 = 0xff ∧
    bothChangedPhysical 320 = 0x62 ∧ bothChangedPhysical 321 = 0xa5 ∧
    bothChangedPhysical 416 = 0xee ∧ bothChangedPhysical 0 = 0xa5 ∧
    bothChangedPhysical 512 = 0xa5 := by decide

theorem byte_string_boundaries : MemoryShape.size (.bytes 0) = 32 ∧
    MemoryShape.size (.bytes 31) = 64 ∧ MemoryShape.size (.bytes 32) = 64 ∧
    MemoryShape.size (.bytes 33) = 96 := by decide

theorem unaligned_same_identity : (bytePlacement 1).address 0 = 129 ∧ (bytePlacement 1).free.val = 513 := ⟨rfl, rfl⟩

#print axioms byte_changed
#print axioms byte_unchanged_whole_heap
#print axioms string_changed
#print axioms two_object_reverse_agreement
end Solidity.Yul.Views.Controls
