import Solidity.Yul.Adapters.P6ByteFamilyCopy
import Solidity.Yul.Adapters.P6ResidualCopyControls
import Solidity.Yul.Views.HeapByteStateControls

/-! Actual string-typed Source object in a three-root heap. A cross-word payload
copy reads nonzero padding into the string without changing its source type or
adding UTF-8 validation. Frame witnesses are synthetic, not allocator traces. -/
namespace Solidity.Yul.Adapters.P6ByteFamilyCopy.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views.Controls

def placement := bytePlacement 0
def first : MixedHeapEntry placement := ⟨0,.bytes .memory,.bytes byteOld,rfl,.bytes byteOld (by decide)⟩
def string : MixedHeapEntry placement := ⟨1,.string .memory,.string stringOld,rfl,.string stringOld (by decide)⟩
def third : MixedHeapEntry placement := ⟨2,.bytes .memory,.bytes byteOther,rfl,.bytes byteOther (by decide)⟩
def entries := [first,string,third]

theorem coverage : CoversMixedHeap entries := by
  intro a present
  have low := byteHeap_present_lt a present
  have choices : a=0 ∨ a=1 ∨ a=2 := by omega
  rcases choices with zero | one | two
  · subst a;exact ⟨first,List.mem_cons_self,rfl⟩
  · subst a;exact ⟨string,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · subst a;exact ⟨third,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩

def carrier := {P6ResidualCopy.Controls.carrier .legacy with
  highWaterWords:=16
  resident:=by decide
  zeroAbove:=by intro i high;have bound:=i.isLt;change 512≤i.val at high;change i.val<512 at bound;omega}
def residual : ByteView := fun a => if a<512 then 165 else 0

theorem fits : MemoryAgreement.Fits carrier residual := by
  intro k high
  change 512≤k at high
  exact if_neg (by omega)

def image := FrameHeap.frameOf carrier placement entries residual fits (by change 512≤512;decide)
def src : ByteSpan image.capacity :=
  ⟨lenU 320 (by decide),lenU 33 (by decide),Or.inr (by change 353≤512;decide)⟩
def dst : ByteSpan image.capacity :=
  ⟨lenU 288 (by decide),lenU 33 (by decide),Or.inr (by change 321≤512;decide)⟩
def reached := P6ByteMemory.copySnapshot image src dst rfl
def payload := readBytes (frameBytes reached) 288 33

def updated := withSourceHeap byteState (byteHeap.write 1
  (Source.Data.string (l:=.memory) payload) (by rfl))

/-- The shared proof constructs a STRING Source action and the whole refreshed
three-root physical view; the surrounding bytes objects are preserved. -/
theorem string_view : ∃ r : InventoryRealization placement,
    updated=withSourceHeap byteState r.heap ∧
    encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
    CoversMixedHeap r.entries ∧
    r.heap.get 0=byteHeap.get 0 ∧ r.heap.get 2=byteHeap.get 2 ∧
    (∀ H,Source.MemOK heapByteEnv H byteState → Source.MemOK heapByteEnv H (withSourceHeap byteState r.heap)) := by
  have initial : frameBytes image=encodeMixedHeap placement entries residual := FrameHeap.frameOf_bytes _ _ _ _ _ _
  have output := payload_copy byteState placement placement .initial entries coverage (by decide) image residual initial
    1 true stringOld rfl src dst rfl (Or.inr (by constructor <;> decide))
  dsimp only at output
  obtain ⟨r,action,view,covered,ids,other,safe,_⟩ := output
  have exactAction : (Source.heapPut 1 ⟨.string .memory,Source.Data.string payload⟩ :
      Source.EM heapByteEnv _ Unit).run byteState=(.ok (),updated) := heapPutConcrete_run _ _ _ (by rfl)
  exact ⟨r,congrArg Prod.snd (exactAction.symm.trans action),view,covered,
    other 0 (by decide),other 2 (by decide),safe⟩

/-- Actual owner bytes observation supports strings without relabeling Data. -/
theorem actual_string_read : (Source.heapBytes (E:=heapByteEnv) (Γ:=[.bytes .memory,.string .memory]) 1).run
    updated=(.ok payload,updated) := by
  first | rfl | decide

/-- The heap retains its genuine string type after the physical copy. -/
theorem string_type : updated.2.heap.ty 1=some (.string .memory) ∧
    updated.2.heap.ty 1≠some (.bytes .memory) := by
  first | decide | rfl

/-- info: (true, 33, 165, 165) -/
#guard_msgs in #eval (decide (payload=0x61::List.replicate 32 165),
  (mload (frameBytes reached) 256).val,(frameBytes reached 321).toNat,(frameBytes reached 352).toNat)
/-- info: true -/
#guard_msgs in #eval decide (readBytes (frameBytes reached) 160 3=byteOld ∧
  readBytes (frameBytes reached) 416 3=byteOther ∧ reached.capacity=512)

end Solidity.Yul.Adapters.P6ByteFamilyCopy.Controls
