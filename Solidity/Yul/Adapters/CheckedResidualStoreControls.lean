import Solidity.Yul.Adapters.CheckedResidualStore
import Solidity.Yul.Adapters.SelectedPhysicalStoreControls

/-! Computed residual plans with actual nominal/byte inventory, reserved words,
compiled writes and later byte-object regrowth. Preparation None is not a
language verdict; current padding is not permanently unowned capacity. -/
namespace Solidity.Yul.Adapters.CheckedResidualStore.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Yul.Compilation
open Solidity.Yul.Adapters.PhysicalSnapshotSlice.Controls (frame)

def base : ByteView := fun a => if 96≤a ∧ a<128 then 0 else 165
def residual : ByteView := mstore base 64 UnchangedControls.placement.free

theorem reserved : ReservedOK residual UnchangedControls.placement.free := by
  constructor
  · exact congrArg Fin.val (mload_mstore base 64 UnchangedControls.placement.free)
  · intro i
    change mstore base 64 UnchangedControls.placement.free (96+i.val)=0
    rw [mstore_outside base 64 (96+i.val) _ (by have bound:=i.isLt;omega)]
    change (if 96≤96+i.val ∧ 96+i.val<128 then (0 : UInt8) else 165)=0
    exact if_pos (by have bound:=i.isLt;omega)

theorem padding_geometry : ResidualWindowDisjoint UnchangedControls.placement
    (generatedHeapEntries UnchangedControls.placement) 227 1 := by
  intro e member
  have bound := generatedHeapEntries_id_bound UnchangedControls.placement e member
  change e.id<2 at bound
  rcases e with ⟨id,ty,data,found,image⟩
  change id<2 at bound
  by_cases zero : id=0
  · subst id
    have fits := image.fits UnchangedControls.placement 0 found
    change image.span≤64 at fits
    apply Or.inr; apply Or.inr; apply Or.inr
    change 128+image.span≤227
    omega
  · have one : id=1 := by omega
    subst id
    change (some ⟨.bytes .memory,UnchangedControls.payload⟩ :
      Option (Σ t,Source.Data NominalMemory.Controls.env.layout t))=some ⟨ty,data⟩ at found
    cases found
    have span : image.span=35 := MemoryImage.bytes_span image
    apply Or.inr; apply Or.inr; apply Or.inr
    change 192+image.span≤227
    omega

def paddingPlan : ResidualWindowPlan UnchangedControls.placement :=
  ⟨227,1,generatedHeapEntries UnchangedControls.placement,
    UnchangedControls.generated_whole_state.1,
    (residualWindowCheck_iff _ _ _ _).mpr ⟨by decide,Or.inr (Or.inr (by decide)),padding_geometry⟩⟩

theorem padding_ready : prepareResidualWindow UnchangedControls.placement 227 1=.ok (some paddingPlan) :=
  prepareResidualWindow_plan paddingPlan

/-- Computed inventory/region preparation leads to actual compiled writeback,
WHOLE Source identity, complete raw reconstruction and BOTH reserved words. -/
theorem padding_write : ∃ next,
    PhysicalSnapshotSlice.applySlice UnchangedControls.placement UnchangedControls.state
      ⟨UnchangedControls.placement,.initial,paddingPlan.entries⟩ frame (PhysicalStore.byteCode 227 0x1fe)
      ⟨[lenU 93 (by decide)],encodeMixedHeap UnchangedControls.placement paddingPlan.entries residual⟩=
      some (⟨[lenU 93 (by decide)],mstore8 (encodeMixedHeap UnchangedControls.placement paddingPlan.entries residual) 227 0x1fe⟩,some next) ∧
    next.1=UnchangedControls.state ∧
    ReservedOK (mstore8 (encodeMixedHeap UnchangedControls.placement paddingPlan.entries residual) 227 0x1fe)
      UnchangedControls.placement.free := by
  obtain ⟨next,actual,same,map,initial,reserved,safe⟩ := prepared_byte UnchangedControls.placement
    UnchangedControls.state UnchangedControls.placement .initial 227 0x1fe paddingPlan padding_ready
    UnchangedControls.heap_profile residual reserved frame [lenU 93 (by decide)]
  exact ⟨next,actual,same,reserved⟩

def prepares (destination : Roadmap.Word) : Bool :=
  match prepareResidualWindow UnchangedControls.placement destination 1 with
  | .ok (some _) => true
  | _ => false
/-- info: [true, true, false, false, false, false, false, true, true] -/
#guard_msgs in #eval ([0,63,64,96,127,128,226,227,300] : List Roadmap.Word).map prepares

def initial : Environment.Slice :=
  ⟨[lenU 93 (by decide)],encodeMixedHeap UnchangedControls.placement paddingPlan.entries residual⟩
def cursor : SnapshotCursor UnchangedControls.placement UnchangedControls.state :=
  ⟨UnchangedControls.placement,.initial,paddingPlan.entries⟩
def written := PhysicalSnapshotSlice.applySlice UnchangedControls.placement UnchangedControls.state cursor frame
  (PhysicalStore.byteCode 227 0x1fe) initial
/-- info: true -/
#guard_msgs in #eval match written with
  | some (physical,some next) => @decide
      (physical.memory 227=254 ∧ physical.memory 228=165 ∧ physical.stack=initial.stack ∧
       ReservedOK physical.memory UnchangedControls.placement.free ∧
       NominalMemory.Controls.aliasRead next.1 .here 0=some (⟨2^256-1,by decide⟩ : Roadmap.Word))
      (by unfold ReservedOK; infer_instance)
  | _ => false

/- The very same byte becomes live after real header growth, with its retained
raw value. A new current-state plan must not reuse the prior ownership mask. -/
/-- info: true -/
#guard_msgs in #eval match written with
  | some (physical,some next) =>
    match PhysicalSnapshotSlice.applySlice UnchangedControls.placement next.1 next.2 frame
        (PhysicalStore.wordCode 192 4) physical with
    | some (grown,some current) =>
      match (Source.heapBytes 1).run current.1 with
      | (.ok payload,_) =>
        let noLongerResidual := match prepareResidualWindow current.2.placement 227 1 with
          | .ok none => true
          | _ => false
        let byteWord := match (Source.readLoc NominalMemory.Controls.readFrame (.memByte 1 3)).run current.1 with
          | (.ok value,_) => value.word
          | _ => none
        decide (payload=[7,0,255,254] ∧ grown.memory 227=254 ∧ grown.memory 228=165 ∧
          noLongerResidual=true ∧ byteWord=some (⟨254*2^248,by decide⟩ : Roadmap.Word))
      | _ => false
    | _ => false
  | _ => false

/- A refused geometry preparation does not change the actual target evaluator:
the published byte program still reaches bytes at64; no refusal is invented. -/
/-- info: true -/
#guard_msgs in #eval (Environment.runSlice frame (PhysicalStore.byteCode 64 255) initial).isSome

end Solidity.Yul.Adapters.CheckedResidualStore.Controls
