import Solidity.Yul.Adapters.P6RetainedArrayHeader
import Solidity.Yul.Adapters.P6RetainedHeapWordStoreControls

/-! Physical header regrowth exposes the SAME dormant original payload.
The actual Source operation is heapPut, not invented length-assignment syntax.
Length3 exceeds the original allocation and remains checked preparation None,
while its physical MSTORE is still a real reached frame. -/
namespace Solidity.Yul.Adapters.P6RetainedArrayHeader.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views ArrayWordRetained.Controls

def image := P6RetainedHeapWordStore.Controls.image
def sink (pipeline : Pipeline) : WordSpan (image pipeline).capacity :=
  ⟨lenU 128 (by decide),by change 128+32≤320;decide⟩
def length : Roadmap.Word := ⟨2,by decide⟩
def values (i : Fin length.val) := uintValueOfWord E.layout (originalWords i)
def out := withSourceHeap current (current.2.heap.write 0 (dynamicMemberData E.layout (.int Source.IntTy.u256) 2 values) (by rfl))
def placement : Placement out.2.heap := retainedMemberArrayPlacement allocated p prior 0 (.int Source.IntTy.u256)
  1 old rfl 2 values (by decide)
def history : RetainedAllocation allocated placement := retainedMemberArray_history allocated p prior 0
  (.int Source.IntTy.u256) 1 old rfl 2 values (by decide)
def reached (pipeline : Pipeline) := store32 (image pipeline) (sink pipeline) (lenU 2 (by decide))

theorem supported (a τ d) (found : current.2.heap.get a=some ⟨τ,d⟩) : InventoryTypeSupported E τ := by
  first | omega | decide | skip
  by_cases same : a=0
  · subst a
    cases found
    exact Or.inl (Or.inr (Or.inl rfl))
  · have missing := current.2.heap.bounded a (by change 1≤a;omega)
    change current.2.heap.cells a=some ⟨τ,d⟩ at found
    rw [missing] at found
    cases found

theorem reads (pipeline : Pipeline) : ∀ e∈generatedHeapEntries p,e.image.Reads (frameBytes (image pipeline)) (p.address e.id) := by
  dsimp only [image]
  rw [P6RetainedHeapWordStore.Controls.initial_image]
  exact encodeMixedHeap_reads p _ (prepareHeapInventory_ok p _ rfl).2.2 seed

theorem live_word : mload memory 160=7 := by
  let selected := memoryArrayImage p 0 (n:=none) 1 (fun _ impossible=>nomatch impossible)
    old words (fun i=>MemoryElement.scalar _ _ (uintValueOfWord_word _ _)) rfl
  have coverage := (prepareHeapInventory_ok p _ rfl).2.1
  have allReads := encodeMixedHeap_reads p _ (prepareHeapInventory_ok p _ rfl).2.2 seed
  have selectedReads := mixedImage_reads_of_coverage p _ coverage memory allReads
    (⟨0,_,_,rfl,selected⟩ : MixedHeapEntry p)
  exact selected.source_word memory (p.address 0) 32 selectedReads 7
    (.arrayElement (n:=none) 1 (fun _ impossible=>nomatch impossible) (fun i=>Source.Data.val (old i))
      ⟨0,by decide⟩ (old ⟨0,by decide⟩) 7 rfl (.scalar _ _ (uintValueOfWord_word _ _)))

theorem dormant_word : mload memory 192=9 := by
  have same : mload patch 192=mload memory 192 := mload_congr patch memory 192
    (fun byte=>mstore_outside _ _ _ _ (by have bound:=byte.isLt;omega))
  exact same.symm.trans dormant_tail.1

theorem tail_reads (pipeline : Pipeline) : ∀ i : Fin length.val,
    mload (frameBytes (image pipeline)) (p.address 0+32+i.val*32)=originalWords i := by
  first | omega | decide | skip
  dsimp only [image]
  rw [P6RetainedHeapWordStore.Controls.initial_image]
  intro i
  have cases_i : i=⟨0,by decide⟩ ∨ i=⟨1,by decide⟩ := by
    have bound : i.val<2 := i.isLt
    apply Or.imp Fin.ext Fin.ext
    change i.val=0 ∨ i.val=1
    omega
  rcases cases_i with rfl | rfl
  · exact live_word
  · exact dormant_word

theorem reserved (pipeline : Pipeline) : ReservedOK (frameBytes (image pipeline)) p.free := by
  dsimp only [image]
  rw [P6RetainedHeapWordStore.Controls.initial_image]
  apply encodeMixedHeap_reserved
  constructor
  · exact congrArg Fin.val (mload_mstore _ 64 allocated.free)
  · intro i
    rw [seed,mstore_outside _ _ _ _ (by have small:=i.isLt;omega),mstore_outside _ _ _ _ (by have small:=i.isLt;omega)]
    have small:=i.isLt
    exact if_neg (by omega)

/-- Complete instantiated transport, including actual P6/MSTORE and original
history writeback; the exact dependent signature is generated in the audit. -/
def actual_transport (pipeline : Pipeline) (stackTail : List Solidity.Backend.Environment.Word) :=
  transport current.2.heap.ty current allocated p prior current_safe supported 0 (.int Source.IntTy.u256)
    (Or.inl (Or.inr (Or.inl rfl))) 1 old rfl length values originalWords
    (fun i=>.scalar _ _ (uintValueOfWord_word _ _)) (by decide)
    (image pipeline) (reads pipeline) (tail_reads pipeline) (reserved pipeline) (sink pipeline) rfl stackTail

theorem source_regrow :
    (Source.heapPut (E:=E) (Γ:=[]) 0 ⟨_,dynamicMemberData E.layout (.int Source.IntTy.u256) 2 values⟩).run current=(.ok (),out) :=
  (actual_transport .legacy []).2.1

theorem dormant_becomes_live :
    (Source.readLoc (E:=E) F (.mem (τ:=.int Source.IntTy.u256) 0 1)).run out=
      (.ok (uintValueOfWord E.layout 9),out) := rfl

def oversized (pipeline : Pipeline) := store32 (image pipeline) (sink pipeline) (lenU 3 (by decide))
theorem beyond_original_none (pipeline : Pipeline) :
    canonicalRetainedState current allocated p prior (generatedHeapEntries p) 0 (.int Source.IntTy.u256)
      (frameBytes (oversized pipeline))=none := by
  first | omega | decide | skip
  dsimp only [oversized]
  rw [P6HeapWordStore.store_image (image pipeline) (sink pipeline) (⟨3,by decide⟩:Roadmap.Word)]
  rw [show (sink pipeline).offset.val.toNat=p.address 0 from rfl]
  unfold canonicalRetainedState
  rw [mload_mstore,if_neg (by decide)]
end Solidity.Yul.Adapters.P6RetainedArrayHeader.Controls
