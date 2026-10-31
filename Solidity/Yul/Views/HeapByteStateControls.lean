import Solidity.Yul.Views.HeapByteControls

/-! Inhabited REAL owner MemOK and source alias reads. Bytes/string alias
compatibility does not change the object's declared heap type. -/
namespace Solidity.Yul.Views.Controls

def byteState : Source.EMState heapByteEnv [.bytes .memory, .string .memory] :=
  ⟨.cons bytesAlias (.cons stringAlias .nil),
    ⟨⟨⟨fun _ => Source.Account.empty _⟩, .empty, []⟩, byteHeap, [], [], ⟨[], .nil⟩⟩⟩
def byteStateAfter := withSourceHeap byteState heapByteAfter
def byteStringStateAfter := withSourceHeap byteState bothHeapAfter

theorem actual_initial_MemOK : Source.MemOK heapByteEnv byteHeap.ty byteState := by
  have hok : Source.HeapOK (E := heapByteEnv) byteHeap :=
    Source.HeapOK.alloc (Source.HeapOK.alloc (Source.HeapOK.alloc Source.HeapOK.empty (.bytes byteOld))
      (.string stringOld)) (.bytes byteOther)
  have shaped : Source.HeapShaped (E := heapByteEnv) byteHeap :=
    Source.HeapShaped.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes byteOther⟩)
      (Source.HeapShaped.alloc (E := heapByteEnv) (x := ⟨.string .memory, .string stringOld⟩)
        (Source.HeapShaped.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes byteOld⟩) (Source.HeapShaped.empty (E := heapByteEnv)) trivial) trivial) trivial
  have inner : Source.HeapInner (E := heapByteEnv) byteHeap :=
    Source.HeapInner.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes byteOther⟩)
      (Source.HeapInner.alloc (E := heapByteEnv) (x := ⟨.string .memory, .string stringOld⟩)
        (Source.HeapInner.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes byteOld⟩) (Source.HeapInner.empty (E := heapByteEnv)) trivial) trivial) trivial
  refine ⟨⟨⟨hok, Source.HeapTy.Le.refl _⟩, ?_⟩, shaped, inner⟩
  exact ⟨⟨.bytes .memory, rfl, rfl⟩, ⟨⟨.bytes .memory, rfl, rfl⟩, trivial⟩⟩

theorem actual_byte_state_writeback : heapByteStateWriteback byteState (bytePlacement 0)
    0 false byteOld rfl byteChangedPhysical = some byteStateAfter := by
  change (heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl byteChangedPhysical).map
    (withSourceHeap byteState) = some byteStateAfter
  rw [byte_changed]
  rfl

theorem actual_string_state_writeback : heapByteStateWriteback byteStateAfter afterBytePlacement
    1 true stringOld rfl bothChangedPhysical = some byteStringStateAfter := by
  change (heapByteWriteback heapByteAfter afterBytePlacement 1 true stringOld rfl bothChangedPhysical).map
    (withSourceHeap byteStateAfter) = some byteStringStateAfter
  rw [string_changed]
  rfl

theorem actual_written_MemOK : Source.MemOK heapByteEnv byteHeap.ty byteStringStateAfter := by
  have first := heapByteStateWriteback_MemOK heapByteEnv byteHeap.ty byteState byteStateAfter (bytePlacement 0)
    0 false byteOld rfl byteChangedPhysical actual_byte_state_writeback actual_initial_MemOK
  exact heapByteStateWriteback_MemOK heapByteEnv byteHeap.ty byteStateAfter byteStringStateAfter afterBytePlacement
    1 true stringOld rfl bothChangedPhysical actual_string_state_writeback first

def byteReadFrame : Source.Fr := ⟨0, 0, 0, false, "HeapBytes", true, 0⟩

theorem actual_alias_source_reads :
    byteStringStateAfter.1.get (.here) = bytesAlias ∧
    byteStringStateAfter.1.get (.there .here) = stringAlias ∧
    (Source.heapBytes (E := heapByteEnv) (Γ := [.bytes .memory, .string .memory]) 0).run byteStringStateAfter =
      (.ok byteNew, byteStringStateAfter) ∧
    (Source.readLoc (E := heapByteEnv) byteReadFrame (.memByte 0 0)).run byteStringStateAfter =
      (.ok (.fixedBytes [0x99] rfl), byteStringStateAfter) ∧
    (Source.heapBytes (E := heapByteEnv) (Γ := [.bytes .memory, .string .memory]) 1).run byteStringStateAfter =
      (.ok stringNew, byteStringStateAfter) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem actual_alias_value_reads (horizon : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon
      (.val (byteStringStateAfter.1.get (.here)))).run byteStringStateAfter = (.ok byteNew, byteStringStateAfter) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon
      (.val (byteStringStateAfter.1.get (.there .here)))).run byteStringStateAfter = (.ok byteNew, byteStringStateAfter) := ⟨rfl, rfl⟩

theorem byte_string_aliases_still_agree :
    bytesAlias.RefOK heapByteEnv byteStringStateAfter.2.heap.ty ∧
    stringAlias.RefOK heapByteEnv byteStringStateAfter.2.heap.ty :=
  ⟨actual_written_MemOK.1.2.1, actual_written_MemOK.1.2.2.1⟩

theorem actual_state_observations_unchanged :
    byteStringStateAfter.2.ex = byteState.2.ex ∧ byteStringStateAfter.2.events = byteState.2.events ∧
    byteStringStateAfter.2.logs = byteState.2.logs ∧ byteStringStateAfter.2.fnLocals = byteState.2.fnLocals := ⟨rfl, rfl, rfl, rfl⟩

#print axioms actual_initial_MemOK
#print axioms actual_written_MemOK
#print axioms actual_alias_source_reads
end Solidity.Yul.Views.Controls
