import Solidity.Yul.Adapters.P6RetainedRegionCopy
import Solidity.Yul.Adapters.P6ByteFamilyCopyControls

/-! Actual selected-entry copying shrinks a string to zero, then regrows it
from untouched raw tail bytes using its original allocation. Current-shape and
oversized controls remain preparation failures, not Source/Yul verdicts. -/
namespace Solidity.Yul.Adapters.P6RetainedRegionCopy.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views.Controls
open P6ByteFamilyCopy.Controls (placement entries carrier)

def residual := mstore (mstore P6ByteFamilyCopy.Controls.residual 448 0) 480 64

theorem fits : MemoryAgreement.Fits carrier residual := by
  intro k high
  change 512≤k at high
  unfold residual
  rw [mstore_outside _ 480 k 64 (by omega),mstore_outside _ 448 k 0 (by omega)]
  exact P6ByteFamilyCopy.Controls.fits k high

def image := FrameHeap.frameOf carrier placement entries residual fits (by change 512≤512;decide)
def zeroSource : ByteSpan image.capacity :=
  ⟨lenU 448 (by decide),lenU 32 (by decide),Or.inr (by change 480≤512;decide)⟩
def headerTarget : ByteSpan image.capacity :=
  ⟨lenU 256 (by decide),lenU 32 (by decide),Or.inr (by change 288≤512;decide)⟩
def zero := prepare byteState placement placement .initial entries 1 true stringOld rfl image zeroSource headerTarget rfl

def growSource : ByteSpan zero.1.capacity :=
  ⟨lenU 480 (by decide),lenU 32 (by decide),Or.inr (by change 512≤512;decide)⟩
def growTarget : ByteSpan zero.1.capacity :=
  ⟨lenU 256 (by decide),lenU 32 (by decide),Or.inr (by change 288≤512;decide)⟩

/-- Selection uses the actual refreshed typed inventory. Missing metadata and
unsupported preparation remain distinct Options; no occupied entry is skipped. -/
def regrow := zero.2.bind (fun r =>
  (r.entries.find? (fun e => e.id==1)).map (fun entry =>
    prepareEntry (withSourceHeap byteState r.heap) placement r.placement r.history r.entries entry
      zero.1 growSource growTarget rfl))

def wrongOrigin : Option Bool := do
  let r ← zero.2
  let entry ← r.entries.find? (fun e => e.id==1)
  pure ((prepareEntry (withSourceHeap byteState r.heap) r.placement r.placement .initial r.entries entry
    zero.1 growSource growTarget rfl).2.isNone)

def oversizeImage := store32 image ⟨lenU 480 (by decide),by change 512≤512;decide⟩ (lenU 65 (by decide))
def overSource : ByteSpan oversizeImage.capacity :=
  ⟨lenU 480 (by decide),lenU 32 (by decide),Or.inr (by change 512≤512;decide)⟩
def overTarget : ByteSpan oversizeImage.capacity :=
  ⟨lenU 256 (by decide),lenU 32 (by decide),Or.inr (by change 288≤512;decide)⟩
def oversized := prepare byteState placement placement .initial entries 1 true stringOld rfl
  oversizeImage overSource overTarget rfl

/-- The seeded zero word is outside every actual live image. -/
theorem zero_word : mload (frameBytes image) 448=0 := by
  rw [image,FrameHeap.frameOf_bytes]
  have raw : mload (encodeMixedHeap placement entries residual) 448=mload residual 448 :=
    mload_congr _ _ 448 (fun i => encodeMixedHeap_residual placement entries residual _ (by
      intro e member
      rcases List.mem_cons.mp member with same | tail
      · subst e;right;change 128+35≤448+i.val;omega
      · rcases List.mem_cons.mp tail with same | tail
        · subst e;right;change 256+65≤448+i.val;omega
        · have same := List.mem_singleton.mp tail
          subst e;right;change 384+35≤448+i.val;omega))
  rw [raw]
  have seed : mload residual 448=mload (mstore P6ByteFamilyCopy.Controls.residual 448 0) 448 :=
    mload_congr _ _ 448 (fun i => mstore_outside _ 480 _ 64 (by have hi:=i.isLt;omega))
  rw [seed,mload_mstore]

/-- Kernel existence and whole-map closure for the actual physical shrink,
with capacity checked against the real original string allocation. -/
theorem shrink_view : ∃ r : InventoryRealization placement,
    zero.2=some r ∧ encodeMixedHeap r.placement r.entries (frameBytes zero.1)=frameBytes zero.1 ∧
    CoversMixedHeap r.entries := by
  have header : mload (frameBytes zero.1) 256=0 :=
    (P6CopyPreparation.copied_word image zeroSource headerTarget rfl rfl).trans zero_word
  have output := region_copy byteState placement placement .initial entries P6ByteFamilyCopy.Controls.coverage
    (by decide) image residual (FrameHeap.frameOf_bytes _ _ _ _ _ _) 1 true stringOld rfl zeroSource headerTarget rfl
    (Or.inr (by constructor <;> decide)) (by
      change (MemoryShape.bytes (mload (frameBytes zero.1) 256).val).size≤96
      rw [header];decide)
  obtain ⟨r,prepared,action,view,covered,_⟩ := output
  exact ⟨r,prepared,view,covered⟩

theorem regrow_word : mload (frameBytes zero.1) 480=64 := by
  have raw : mload (frameBytes image) 480=mload residual 480 := by
    rw [image,FrameHeap.frameOf_bytes]
    exact mload_congr _ _ 480 (fun i => encodeMixedHeap_residual placement entries residual _ (by
      intro e member
      rcases List.mem_cons.mp member with same | tail
      · subst e;right;change 128+35≤480+i.val;omega
      · rcases List.mem_cons.mp tail with same | tail
        · subst e;right;change 256+65≤480+i.val;omega
        · have same := List.mem_singleton.mp tail
          subst e;right;change 384+35≤480+i.val;omega))
  have before : mload (frameBytes image) 480=64 := raw.trans (mload_mstore _ 480 64)
  have untouched := mload_congr (frameBytes zero.1) (frameBytes image) 480 (fun i =>
    P6ByteMemory.copy_outside image zeroSource headerTarget rfl _ (Or.inr (by
      change 256+32≤480+i.val;omega)))
  exact untouched.trans before

/-- Kernel two-step preparation existence: the second step uses the ACTUAL
zero-length result's refreshed inventory and original allocation lineage. -/
theorem kernel_regrow : ∃ r : InventoryRealization placement,
    ∃ found : r.heap.get 1=some ⟨.string .memory,Source.Data.string []⟩,
    ∃ next : InventoryRealization placement,
      zero.2=some r ∧
      (prepare (withSourceHeap byteState r.heap) placement r.placement r.history r.entries
        1 true [] found zero.1 growSource growTarget rfl).2=some next ∧
      encodeMixedHeap next.placement next.entries
        (frameBytes (P6ByteMemory.copySnapshot zero.1 growSource growTarget rfl))=
        frameBytes (P6ByteMemory.copySnapshot zero.1 growSource growTarget rfl) ∧
      next.heap.get 1=some ⟨.string .memory,Source.Data.string
        (readBytes (frameBytes (P6ByteMemory.copySnapshot zero.1 growSource growTarget rfl)) 288 64)⟩ := by
  have header0 : mload (frameBytes zero.1) 256=0 :=
    (P6CopyPreparation.copied_word image zeroSource headerTarget rfl rfl).trans zero_word
  have first := region_copy byteState placement placement .initial entries P6ByteFamilyCopy.Controls.coverage
    (by decide) image residual (FrameHeap.frameOf_bytes _ _ _ _ _ _) 1 true stringOld rfl zeroSource headerTarget rfl
    (Or.inr (by constructor <;> decide)) (by
      change (MemoryShape.bytes (mload (frameBytes zero.1) 256).val).size≤96
      rw [header0];decide)
  obtain ⟨r,prepared,action,view,covered,ids,other,safe,types,count,addresses,free,root⟩ := first
  have found : r.heap.get 1=some ⟨.string .memory,Source.Data.string []⟩ := by
    change r.heap.get 1=some ⟨.string .memory,Source.Data.string
      (readBytes (frameBytes zero.1) 288 (mload (frameBytes zero.1) 256).val)⟩ at root
    rw [header0] at root
    exact root
  have header64 : mload (frameBytes (P6ByteMemory.copySnapshot zero.1 growSource growTarget rfl)) 256=64 :=
    (P6CopyPreparation.copied_word zero.1 growSource growTarget rfl rfl).trans regrow_word
  have address : r.placement.address 1=256 := congrFun r.history.addresses 1
  have distinct : (r.entries.map MixedHeapEntry.id).Nodup := by rw [ids];decide
  have second := region_copy (withSourceHeap byteState r.heap) placement r.placement r.history r.entries covered
    distinct zero.1 (frameBytes zero.1) view.symm 1 true [] found growSource growTarget rfl
    (Or.inr (by rw [address];constructor <;> decide)) (by rw [address,header64];decide)
  obtain ⟨next,regrown,run,reencoded,covers,identity,preserved,ok,ty,n,addr,fmp,read⟩ := second
  rw [address,header64] at read
  exact ⟨r,found,next,prepared,regrown,reencoded,read⟩

/-- info: (true, true, true, true) -/
#guard_msgs in #eval (zero.2.isSome,regrow.isSome,
  match regrow with | some (_,r) => r.isSome | none => false,
  wrongOrigin==some true)
/-- info: (0, 32, 64, 96, true) -/
#guard_msgs in #eval match zero.2,regrow with
  | some z,some (_,some r) =>
    let bytes := (Source.heapBytes (E:=heapByteEnv) (Γ:=[.bytes .memory,.string .memory]) 1).run
      (withSourceHeap byteState r.heap)
    match bytes with
    | (.ok bs,_) => (0,z.placement.shape 1 |>.size,bs.length,r.placement.shape 1 |>.size,
        decide (bs=stringOld++List.replicate 31 165))
    | _ => (1,0,0,0,false)
  | _,_ => (2,0,0,0,false)
/-- info: (true, 65, 165) -/
#guard_msgs in #eval (oversized.2.isNone,(mload (frameBytes oversized.1) 256).val,
  (frameBytes oversized.1 352).toNat)
/-- info: true -/
#guard_msgs in #eval match regrow with
  | some (frame,some r) => decide (readBytes (frameBytes frame) 160 3=byteOld ∧
      readBytes (frameBytes frame) 416 3=byteOther ∧ frameBytes frame 321=165 ∧
      r.placement.free=placement.free)
  | _ => false

end Solidity.Yul.Adapters.P6RetainedRegionCopy.Controls
