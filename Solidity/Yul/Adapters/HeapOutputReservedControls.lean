import Solidity.Yul.Adapters.HeapOutputReserved
import Solidity.Yul.Adapters.HeapCallOutputControls

/-! A real six-object Source heap roundtrips after an output to the object
complement even when that output corrupts the reserved zero word. This pins
why Source writeback identity is not reserved-word safety. Safe and empty
outputs preserve the actual initial reserved bytes without cleaning them. -/
namespace Solidity.Yul.Adapters.HeapOutputReserved.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open HeapCallOutput.Controls (carrier room)

def residual : ByteView := fun k=>if k<2048 then mixedResidual k else 0
theorem fits (pipeline : Pipeline) : MemoryAgreement.Fits (carrier pipeline) residual := by
  intro k high
  exact if_neg (by change 2048≤k at high;omega)
theorem reserved : ReservedOK residual mixedPlacement.free := by
  constructor
  · have same := mload_congr residual mixedResidual 64 (fun i=>if_pos (by have small:=i.isLt;omega))
    exact (congrArg Fin.val same).trans mixed_reserved_initial.1
  · intro i
    exact (if_pos (by have small:=i.isLt;omega)).trans (mixed_reserved_initial.2 i)
def initial (pipeline : Pipeline) := FrameHeap.frameOf (carrier pipeline) mixedPlacement
  (generatedHeapEntries mixedPlacement) residual (fits pipeline) (room pipeline)
theorem initial_reserved (pipeline : Pipeline) : ReservedOK (frameBytes (initial pipeline)) mixedPlacement.free :=
  FrameHeap.frame_reserved _ _ _ _ _ _ reserved

def input (pipeline : Pipeline) : ByteSpan (initial pipeline).capacity :=
  ⟨lenU 0 (by decide),lenU 0 (by decide),Or.inl rfl⟩
def badOutput (pipeline : Pipeline) : ByteSpan (initial pipeline).capacity :=
  ⟨lenU 96 (by decide),lenU 1 (by decide),Or.inr (by change 96+1≤2048;decide)⟩
def bad (pipeline : Pipeline) := RawPhysicalCallAccess.reached (initial pipeline) (input pipeline) (badOutput pipeline) [1]

/-- Actual owner writeback succeeds and keeps the whole Source state. -/
theorem source_unchanged (pipeline : Pipeline) :
    FrameHeap.writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (bad pipeline)=
      .ok (some (.ok (),mixedState)) := by
  exact (HeapCallOutput.residual_unchanged mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    residual mixed_actual_MemOK generated_mixed_types_supported (carrier pipeline) (fits pipeline) (room pipeline)
    (input pipeline) (badOutput pipeline) [1] (by
      intro e member
      right
      have present : (mixedHeap.cells e.id).isSome := by
        change (mixedState.2.heap.get e.id).isSome=true
        rw [e.found]
        rfl
      have start := mixedPlacement.starts e.id present
      change 96+1≤mixedPlacement.address e.id
      omega)).1

theorem bad_byte (pipeline : Pipeline) : frameBytes (bad pipeline) 96=1 := by
  dsimp only [bad]
  rw [RawPhysicalCallAccess.image,RawPhysicalCallOutput.image]
  exact Environment.writeBytes_at [1] 96 0 _ (by decide)

theorem not_reserved (pipeline : Pipeline) : ¬ReservedOK (frameBytes (bad pipeline)) mixedPlacement.free := by
  intro claimed
  have zero := claimed.2 ⟨0,by decide⟩
  change frameBytes (bad pipeline) 96=0 at zero
  rw [bad_byte] at zero
  exact (by decide : (1:UInt8)≠0) zero

def goodOutput (pipeline : Pipeline) : ByteSpan (initial pipeline).capacity :=
  ⟨lenU 1800 (by decide),lenU 16 (by decide),Or.inr (by change 1800+16≤2048;decide)⟩
theorem safe_preserves (pipeline : Pipeline) :
    ReservedOK (frameBytes (RawPhysicalCallAccess.reached (initial pipeline) (input pipeline) (goodOutput pipeline) [17,255]))
      mixedPlacement.free :=
  preserve_interval _ _ _ _ _ (initial_reserved pipeline) (Or.inr (Or.inr (by change 128≤1800;decide)))

/-- The same requested bad span is harmless for empty returndata. -/
theorem empty_preserves (pipeline : Pipeline) :
    ReservedOK (frameBytes (RawPhysicalCallAccess.reached (initial pipeline) (input pipeline) (badOutput pipeline) []))
      mixedPlacement.free :=
  preserve_interval _ _ _ _ _ (initial_reserved pipeline) (Or.inl rfl)
end Solidity.Yul.Adapters.HeapOutputReserved.Controls
