import Solidity.Yul.Adapters.P6MultiRootByteRefresh
import Solidity.Yul.Adapters.P6MultiRootByteControls

/-! Two real plans share one reached source state and finite frame. The second
preparation is derived, not resupplied. A late failure retains the first plan
and skips its remaining suffix; reusing stale source state changes the bytes. -/
namespace Solidity.Yul.Adapters.P6MultiRootByteRefresh.Controls
open Solidity.Yul.Views Solidity.Yul.Views.MultiRootByteWrites
open Solidity.Yul.Views.Controls Solidity.Yul.Views.MultiRootByteWrites.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6MultiRootByte.Controls

def firstPlan := requests.take 2
def secondPlan := requests.drop 2
def firstOut (pipeline : Pipeline) := P6MultiRootByte.run mixedReadFrame 0 firstPlan mixedState mixedPlacement
  StructWordHeap.Controls.support (image pipeline) (room pipeline)

theorem first_success (pipeline : Pipeline) : (firstOut pipeline).1.1=.ok () := by
  first | (simp only;done) | decide | omega | rfl

theorem derived_sequence (pipeline : Pipeline) (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) :
    ∃ q : Placement (firstOut pipeline).1.2.2.heap,
      ∃ nextSupport : ∀ a τ d,(firstOut pipeline).1.2.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported mixedEnv τ,
      ∃ nextRoom : q.free.val≤(firstOut pipeline).2.highWaterWords*32,
        Source.MemOK mixedEnv H (firstOut pipeline).1.2 ∧
        let final := P6MultiRootByte.run mixedReadFrame 0 secondPlan (firstOut pipeline).1.2 q
          nextSupport (firstOut pipeline).2 nextRoom
        final.1=(.error (.stuck "not bytes"),after) ∧
        frameBytes final.2=frameBytes (P6MultiRootByte.Controls.reached pipeline).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have prepared := refresh H mixedPlacement mixedReadFrame 0 firstPlan mixedState mixedPlacement
    (retainInitial _ _) ok StructWordHeap.Controls.support (image pipeline) (room pipeline)
    (initial_reads pipeline) (initial_reserved pipeline)
  obtain ⟨q,addresses,free,history,safe,nextSupport,nextRoom,reads,reserved,wb⟩ := prepared
  refine ⟨q,nextSupport,nextRoom,safe,?_⟩
  have sequence := append_success mixedReadFrame 0 firstPlan secondPlan mixedState mixedPlacement
    StructWordHeap.Controls.support (image pipeline) (room pipeline) q addresses nextSupport nextRoom (first_success pipeline)
  have joined : firstPlan++secondPlan=requests := rfl
  rw [joined] at sequence
  have direct : coupled mixedReadFrame 0 mixedPlacement.address requests mixedState (frameBytes (image pipeline))=
      ((.error (.stuck "not bytes"),after),frameBytes (P6MultiRootByte.Controls.reached pipeline).2) := by
    apply Prod.ext
    · exact (source mixedReadFrame 0 mixedPlacement.address requests mixedState _).trans actual_source
    · exact (P6MultiRootByte.bytes mixedReadFrame 0 requests mixedState mixedPlacement
        StructWordHeap.Controls.support (image pipeline) (room pipeline)).symm
  have same := sequence.symm.trans direct
  exact ⟨congrArg Prod.fst same,congrArg Prod.snd same⟩

/-- The real failed prefix prevents even a valid following write. -/
theorem failed_prefix_skips (pipeline : Pipeline) :
    coupled mixedReadFrame 0 mixedPlacement.address (requests++[(5,0,0xaa)]) mixedState (frameBytes (image pipeline))=
      coupled mixedReadFrame 0 mixedPlacement.address requests mixedState (frameBytes (image pipeline)) := by rfl

/-- Starting stage two from the original Source loses the first stage's string
mutation. This compares actual bytes, without a hash-injectivity premise. -/
theorem stale_source_negative :
    (program mixedReadFrame 0 secondPlan).run mixedState≠(.error (.stuck "not bytes"),after) := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro same
  have lost := congrArg (fun result : Source.R Unit × Source.EMState mixedEnv _ =>
    (Source.heapBytes 1).run result.2) same
  have different : ([0xff,0x61] : List UInt8)≠[0x80,0x61] := by decide
  have values := congrArg Prod.fst lost
  change (Except.ok ([0xff,0x61] : List UInt8) : Source.R (List UInt8))=Except.ok [0x80,0x61] at values
  exact different (Except.ok.inj values)
end Solidity.Yul.Adapters.P6MultiRootByteRefresh.Controls
