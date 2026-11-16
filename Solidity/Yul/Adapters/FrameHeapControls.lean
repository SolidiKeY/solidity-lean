import Solidity.Yul.Adapters.FrameHeap
import Solidity.Yul.Adapters.ImageIdentity
import Solidity.Yul.Views.MixedHeapControls
import Solidity.Yul.Views.HeapEnumerationBoundaryControls

namespace Solidity.Yul.Adapters.FrameHeap.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views Solidity.Yul.Views.Controls
private def C : Contract := {vars:=[]}
private def carrier (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨12,2,pipeline,5,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=2048,aligned:=⟨64,rfl⟩,data:=fun _=>0,highWaterWords:=64,
   resident:=by decide,zeroAbove:=by intro i h;have hi:=i.isLt;omega}
private def residual (free : Roadmap.Word) : ByteView :=
  mstore (mstore (fun k=>if k<2048 then 165 else 0) 64 free) 96 0
private theorem fits (pipeline : Pipeline) (free : Roadmap.Word) :
    MemoryAgreement.Fits (carrier pipeline) (residual free) := by
  intro k high
  change 2048≤k at high
  rw [residual,mstore_outside _ _ _ _ (by omega),mstore_outside _ _ _ _ (by omega)]
  exact if_neg (by omega)
private theorem room (pipeline : Pipeline) : mixedPlacement.free.val≤(carrier pipeline).highWaterWords*32 := by
  change 1664≤64*32
  decide

private theorem supported_entry (e : MixedHeapEntry mixedPlacement) (member : e∈mixedEntries) :
    InventoryTypeSupported mixedEnv e.ty := by
  simp only [mixedEntries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · exact Or.inl (Or.inr (Or.inl rfl))
  · intro τ ht
    change τ∈[.bool,.int .u256,.bytes .memory,.bytes .memory,mixedArrayTy] at ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    all_goals exact Or.inl (Or.inr (Or.inr rfl))
  · exact Or.inl (Or.inr (Or.inr rfl))
  · trivial
private theorem supported (a : Nat) (τ : Source.STy) (d : Source.Data mixedLayout τ)
    (found : mixedHeap.get a=some ⟨τ,d⟩) : InventoryTypeSupported mixedEnv τ := by
  have present : (mixedHeap.cells a).isSome := by rw [show mixedHeap.cells a=some ⟨τ,d⟩ from found];rfl
  obtain ⟨e,member,same⟩:=mixed_coverage a present
  have eq:=Option.some.inj (found.symm.trans (same ▸ e.found))
  cases eq
  exact supported_entry e member

/-- No supplied entry list/view/inverse: computed from actual owner heap and
its real Placement, including structs, arrays and shared child pointers. -/
theorem six_root_roundtrip (pipeline : Pipeline) : ∃ image : FrameMem C [],
    prepareFrame (carrier pipeline) mixedPlacement (residual mixedPlacement.free) (fits _ _) (room _)=.ok image ∧
    CoversMixedHeap (generatedHeapEntries mixedPlacement) ∧
    ((generatedHeapEntries mixedPlacement).map MixedHeapEntry.id).Nodup ∧
    frameBytes image=encodeMixedHeap mixedPlacement (generatedHeapEntries mixedPlacement) (residual mixedPlacement.free) ∧
    enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _)
      (frameBytes image)=.ok (some (.ok (),mixedState)) ∧
    image.st=(carrier pipeline).st ∧ image.key=(carrier pipeline).key ∧
    image.capacity=(carrier pipeline).capacity ∧ image.highWaterWords=(carrier pipeline).highWaterWords :=
  owner_roundtrip _ mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixed_actual_MemOK supported
    (carrier pipeline) (residual mixedPlacement.free) (fits _ _) (room _)

/-- Current owner permits calldata refs; ordinary memory-member support does
not. The compatibility repair uses the latter, never false RefOK. -/
theorem calldata_owner_permitted (H : Source.HeapTy) :
    Source.Val.RefOK mixedEnv H (Source.Val.cdRef (τ:=.bytes .calldata) rfl 0 0) := trivial

theorem calldata_not_memory_member : ¬ExtendedMemberType mixedLayout (.bytes .calldata) := by
  intro h
  rcases extendedMember_location h with no | memory
  · cases no
  · cases memory

private def observed (pipeline : Pipeline) : List Nat :=
  match prepareFrame (carrier pipeline) mixedPlacement (residual mixedPlacement.free) (fits _ _) (room _) with
  | .error _=>[]
  | .ok image=>
    let m:=frameBytes image
    [(mload m 128).val,(mload m 384).val,(mload m 640).val,(mload m 672).val,
      (mload m 896).val,(mload m 928).val,(mload m 960).val,(mload m 992).val,
      (mload m 1024).val,(mload m 1152).val,(mload m 1184).val,(mload m 1216).val,
      (mload m 64).val,(mload m 96).val,(m 180).toNat,(m 2047).toNat,(m 2048).toNat]
/-- info: [3, 2, 7, 9, 1, 7, 128, 128, 1152, 2, 128, 128, 1664, 0, 165, 165, 0] -/
#guard_msgs in #eval observed .legacy
/-- info: [3, 2, 7, 9, 1, 7, 128, 128, 1152, 2, 128, 128, 1664, 0, 165, 165, 0] -/
#guard_msgs in #eval observed .viaIR
/-- info: false -/
#guard_msgs in #eval decide (observed .legacy=[3,2,7,9,1,7,128,384,1152,2,128,128,1664,0,165,165,0])
theorem unsupported_builder (pipeline : Pipeline) :
    prepareFrame (carrier pipeline) enumerationDanglingPlacement (residual enumerationDanglingPlacement.free)
      (fits _ _) (by change 512≤64*32;decide)=.error [2] := by
  unfold prepareFrame
  rw [enumeration_occupied_failure_exact.1]
  rfl

theorem after_roundtrip_aliases (pipeline : Pipeline) (horizon : Nat) :
    ∃ image : FrameMem C [], ∃ after : Source.EMState mixedEnv
      [.bytes .memory,.string .memory,mixedArrayTy,.struct .memory mixedName],
      prepareFrame (carrier pipeline) mixedPlacement (residual mixedPlacement.free) (fits _ _) (room _)=.ok image ∧
      writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) image=.ok (some (.ok (),after)) ∧
      (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (after.1.get .here))).run after=
        (.ok mixedChild,after) ∧
      (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (after.1.get (.there .here)))).run after=
        (.ok mixedChild,after) := by
  obtain ⟨image,build,coverage,distinct,bytes,source,metadata⟩:=six_root_roundtrip pipeline
  exact ⟨image,mixedState,build,source,(mixed_source_alias_reads horizon).1,(mixed_source_alias_reads horizon).2⟩
private def built (pipeline : Pipeline) : FrameMem C [] :=
  frameOf (carrier pipeline) mixedPlacement (generatedHeapEntries mixedPlacement)
    (residual mixedPlacement.free) (fits _ _) (room _)
theorem computed_entries_identity : generatedHeapEntries mixedPlacement=mixedEntries := by
  apply ImageIdentity.entries_eq
  rw [generatedHeapEntries_ids]
  decide

private theorem built_bytes (pipeline : Pipeline) :
    frameBytes (built pipeline)=encodeMixedHeap mixedPlacement mixedEntries (residual mixedPlacement.free) := by
  rw [built,frameOf_bytes,computed_entries_identity]

private def writeSpan (pipeline : Pipeline) : WordSpan (built pipeline).capacity :=
  ⟨lenU 928 (by decide),by change 928+32≤2048;decide⟩
private def changed (pipeline : Pipeline) : FrameMem C [] :=
  store32 (built pipeline) (writeSpan pipeline) (lenU 77 (by decide))

theorem actual_mstore (pipeline : Pipeline) (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨(writeSpan pipeline).offset::lenU 77 (by decide)::tail,frameBytes (built pipeline)⟩=
      some ⟨tail,frameBytes (changed pipeline)⟩ := (frame_store32_target _ _ _ _).1

private def successStatus (pipeline : Pipeline) : Bool :=
  match writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (changed pipeline) with
  | .ok (some _)=>true
  | _=>false

theorem changed_prepares (pipeline : Pipeline) : ∃ result,
    writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (changed pipeline)=.ok (some result) := by
  have raw : frameBytes (changed pipeline)=Environment.writeBytes
      (encodeMixedHeap mixedPlacement mixedEntries (residual mixedPlacement.free)) 928 (Semantics.wordBytes 77) := by
    rw [changed,frameBytes_store32,built_bytes]
    rfl
  have decoded : (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries
      (frameBytes (changed pipeline))).isSome := by
    rw [raw]
    decide
  obtain ⟨updates,yes⟩:=Option.isSome_iff_exists.mp decoded
  refine ⟨(runInventoryUpdates updates).run mixedState,?_⟩
  unfold writeback enumeratedMemoryWriteback
  rw [ownerMemOK_prepares_inventory _ mixedState mixedPlacement mixed_actual_MemOK supported,computed_entries_identity]
  change Except.ok (inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries (frameBytes (changed pipeline)))=Except.ok _
  unfold inventoryStateWriteback
  rw [yes]
  rfl

private def observedChanged (pipeline : Pipeline) : List Nat :=
  match writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (changed pipeline) with
  | .ok (some (.ok (),s))=>
    match (Source.readLoc (E:=mixedEnv) mixedReadFrame (Γ:=[.bytes .memory,.string .memory,mixedArrayTy,.struct .memory mixedName])
        (τ:=.int .u256) (.mem 3 1)).run s with
    | (.ok value,_)=>[1,(Solidity.Backend.MemoryOps.calldataUint (.val value)).val.toNat,(frameBytes (changed pipeline) 180).toNat,s.2.heap.next]
    | _=>[2]
  | .ok none=>[0]
  | _=>[3]
/-- info: [1, 77, 165, 6] -/
#guard_msgs in #eval observedChanged .legacy
/-- info: [1, 77, 165, 6] -/
#guard_msgs in #eval observedChanged .viaIR
/-- info: false -/
#guard_msgs in #eval decide (observedChanged .legacy=[1,7,165,6])
theorem changed_reached (pipeline : Pipeline) : ∃ realized : InventoryRealization mixedPlacement,
    writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (changed pipeline)=
      .ok (some (.ok (),withSourceHeap mixedState realized.heap)) ∧
    CoversMixedHeap realized.entries ∧ (realized.entries.map MixedHeapEntry.id).Nodup ∧
    encodeMixedHeap realized.placement realized.entries (frameBytes (changed pipeline))=frameBytes (changed pipeline) ∧
    realized.heap.ty=mixedHeap.ty ∧ realized.heap.next=mixedHeap.next ∧
    realized.placement.address=mixedPlacement.address ∧ realized.placement.free=mixedPlacement.free ∧
    Source.MemOK mixedEnv mixedHeap.ty (withSourceHeap mixedState realized.heap) := by
  obtain ⟨result,step⟩:=changed_prepares pipeline
  obtain ⟨realized,run,coverage,distinct,raw,types,next,addresses,free,mem⟩:=
    reached mixedState mixedPlacement mixedPlacement (retainInitial _ _) (changed pipeline) result step
  refine ⟨realized,?_,coverage,distinct,raw,types,next,addresses,free,?_⟩
  · rw [←run];exact step
  · have good:=mem mixedHeap.ty mixed_actual_MemOK
    rw [run] at good
    exact good

private def badPointer (pipeline : Pipeline) : FrameMem C [] :=
  store32 (built pipeline) ⟨lenU 960 (by decide),by change 960+32≤2048;decide⟩ (lenU 77 (by decide))
private def badStatus (pipeline : Pipeline) : Nat :=
  match writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (badPointer pipeline) with
  | .error _=>2
  | .ok none=>0
  | .ok (some _)=>1
/-- info: 0 -/
#guard_msgs in #eval badStatus .legacy
/-- info: 0 -/
#guard_msgs in #eval badStatus .viaIR
/-- info: false -/
#guard_msgs in #eval decide (badStatus .legacy=1)
/-- The padding/gap interval 180..212 is outside EVERY computed object
image in the inhabited six-root heap, including shared-child pointer roots. -/
theorem residual_interval : ∀ e∈mixedEntries,
    mixedPlacement.address e.id+e.image.span≤180 ∨ 180+32≤mixedPlacement.address e.id := by
  intro e member
  simp only [mixedEntries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def residualChanged (pipeline : Pipeline) : FrameMem C [] :=
  store32 (built pipeline) ⟨lenU 180 (by decide),by change 180+32≤2048;decide⟩
    (lenU 77 (by decide))
private def residualObserved (pipeline : Pipeline) : List Nat :=
  match writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (residualChanged pipeline) with
  | .ok (some (.ok (),s))=>
    match (Source.readLoc (E:=mixedEnv) mixedReadFrame (Γ:=[.bytes .memory,.string .memory,mixedArrayTy,.struct .memory mixedName])
        (τ:=.int .u256) (.mem 3 1)).run s with
    | (.ok value,_)=>[1,(Solidity.Backend.MemoryOps.calldataUint (.val value)).val.toNat,
        (mload (frameBytes (residualChanged pipeline)) 180).val,
        (frameBytes (residualChanged pipeline) 212).toNat,s.2.heap.next]
    | _=>[2]
  | .ok none=>[0]
  | _=>[3]
/-- info: [1, 7, 77, 165, 6] -/
#guard_msgs in #eval residualObserved .legacy
/-- info: [1, 7, 77, 165, 6] -/
#guard_msgs in #eval residualObserved .viaIR
/-- info: false -/
#guard_msgs in #eval decide (residualObserved .legacy=[1,77,77,165,6])
/-- info: false -/
#guard_msgs in #eval decide (residualObserved .viaIR=[1,7,0,165,6])
/- An overlapping object-word write is NOT justified by the residual rule. -/
/-- info: false -/
#guard_msgs in #eval decide (mixedPlacement.address mixedEntry3.id+mixedEntry3.image.span≤928 ∨
  928+32≤mixedPlacement.address mixedEntry3.id)

private theorem byte_outside : ∀ e∈generatedHeapEntries mixedPlacement,
    mixedPlacement.address e.id+e.image.span≤180 ∨ 180+3≤mixedPlacement.address e.id := by
  rw [computed_entries_identity]
  intro e member
  have bounds := residual_interval e member
  omega

private def residualByteSpan (pipeline : Pipeline) : ByteSpan (built pipeline).capacity :=
  ⟨lenU 180 (by decide),lenU 3 (by decide),Or.inr (by change 180+3≤2048;decide)⟩
private def byteChanged (pipeline : Pipeline) : FrameMem C [] :=
  P6ByteMemory.writeSpan (built pipeline) (residualByteSpan pipeline) [0,255,2] rfl

/-- Actual six-root Source state is unchanged after a real bounded byte write,
not just its selected read projection. Includes both pipeline tags. -/
theorem residual_byte_source (pipeline : Pipeline) :
    writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (byteChanged pipeline)=
      .ok (some (.ok (),mixedState)) :=
  (residual_span_unchanged mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    (residual mixedPlacement.free) mixed_actual_MemOK supported (carrier pipeline) (fits _ _) (room _)
    (residualByteSpan pipeline) [0,255,2] rfl byte_outside).1

/-- info: ([0, 255, 2, 165], 64) -/
#guard_msgs in #eval
  ((Environment.readMemory (frameBytes (byteChanged .legacy)) 180 4).map UInt8.toNat,
    (byteChanged .legacy).highWaterWords)
/-- info: false -/
#guard_msgs in #eval decide ((frameBytes (byteChanged .viaIR) 181).toNat=165)

private def sliceFrame : Source.Fr := {mixedReadFrame with cd:=[9,0,255,2,8]}

/-- An actual calldata producer and mixed-heap decoder compose without a
caller-supplied final physical or Source agreement. -/
theorem calldata_heap (pipeline : Pipeline) : ∃ image : FrameMem C [],
    (SourceSliceFrame.consume (built pipeline) (residualByteSpan pipeline) sliceFrame
      0 0 5 1 4 false).run mixedState=(.ok ([0,255,2],some image),mixedState) ∧
    writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) image=
      .ok (some (.ok (),mixedState)) := by
  obtain ⟨image,run,source,raw,read⟩ := calldata_residual_unchanged mixedHeap.ty mixedState
    mixedPlacement mixedPlacement (retainInitial _ _) (residual mixedPlacement.free)
    mixed_actual_MemOK supported (carrier pipeline) (fits _ _) (room _) (residualByteSpan pipeline)
    sliceFrame 0 0 5 1 4 false (by decide) (by decide) (by decide) rfl byte_outside
  exact ⟨image,run,source⟩

/-- info: ([0, 255, 2], [0, 255, 2, 165]) -/
#guard_msgs in #eval
  match (SourceSliceFrame.consume (built .legacy) (residualByteSpan .legacy) sliceFrame
    0 0 5 1 4 false).run mixedState with
  | (.ok (payload,some image),_) =>
      (payload.map UInt8.toNat,(Environment.readMemory (frameBytes image) 180 4).map UInt8.toNat)
  | _ => ([],[])
/-- info: true -/
#guard_msgs in #eval
  match (SourceSliceFrame.consume (built .viaIR) (residualByteSpan .viaIR) sliceFrame
    0 0 5 1 2 false).run mixedState with
  | (.ok ([0],none),_) => true
  | _ => false

end Solidity.Yul.Adapters.FrameHeap.Controls
