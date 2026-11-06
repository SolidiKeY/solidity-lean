import Solidity.Yul.Views.MixedHeapOrder
import Solidity.Yul.Views.HeapEnumerationControls

/-! Six actual heterogeneous roots, including two references to the same child,
are encoded in reverse order with whole-source unchanged writeback. Missing
entries remain a genuine coverage failure, not a valid permutation. -/
namespace Solidity.Yul.Views.Controls
private def orderEntries := generatedHeapEntries mixedPlacement
private def orderResidual : ByteView := fun i=>if i=200 then 99 else if i=1700 then 170 else 0
private def forward := encodeMixedHeap mixedPlacement orderEntries orderResidual
private def backward := encodeMixedHeap mixedPlacement orderEntries.reverse orderResidual

theorem reverse_whole_map : backward=forward :=
  encodeMixedHeap_perm mixedPlacement (List.reverse_perm orderEntries)
    ((List.reverse_perm orderEntries).symm.map MixedHeapEntry.id |>.nodup (generatedHeapEntries_nodup mixedPlacement)) orderResidual

theorem repeat_whole_map : encodeMixedHeap mixedPlacement orderEntries backward=backward := by
  rw [reverse_whole_map]
  exact encodeMixedHeap_idempotent mixedPlacement orderEntries (generatedHeapEntries_nodup mixedPlacement) orderResidual

theorem reverse_source_every_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) :
    enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) backward=
      .ok (some (.ok (),mixedState)) :=
  generated_permuted_writeback H mixedState mixedPlacement ok generated_mixed_types_supported
    orderEntries.reverse (List.reverse_perm _) orderResidual

theorem reverse_source_inhabited :
    enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) backward=
      .ok (some (.ok (),mixedState)) := reverse_source_every_H mixedHeap.ty mixed_actual_MemOK

theorem exact_gap_and_tail : backward 200=99 ∧ backward 1700=170 := by
  rw [reverse_whole_map]
  constructor
  · apply encodeMixedHeap_residual mixedPlacement orderEntries orderResidual 200
    intro e member
    have span := e.image.fits mixedPlacement e.id e.found
    change e.image.span≤(mixedShape e.id).size at span
    by_cases zero : e.id=0
    · have bound : e.image.span≤64 := by rw [zero] at span;exact span
      right
      change 128+e.id*256+e.image.span≤200
      rw [zero]
      omega
    · left
      change 200<128+e.id*256
      omega
  · exact encodeMixedHeap_after_free mixedPlacement orderEntries orderResidual 1700 (by decide)

/-- info: [3, 2, 7, 9, 1, 7, 128, 128, 1152, 2, 128, 128, 3, 17, 255, 99, 170] -/
#guard_msgs in #eval
  [128,384,640,672,896,928,960,992,1024,1152,1184,1216,1408].map
    (fun a=>(mload backward a).val) ++
  [160,416,200,1700].map (fun a=>(backward a).toNat)
/-- info: (3, 0) -/
#guard_msgs in #eval ((mload backward 1408).val,
  (mload (encodeMixedHeap mixedPlacement (orderEntries.take 5) orderResidual) 1408).val)
/-- info: false -/
#guard_msgs in #eval (backward 200==0 && backward 1700==0)
end Solidity.Yul.Views.Controls
