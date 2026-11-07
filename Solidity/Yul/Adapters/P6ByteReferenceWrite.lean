import Solidity.Yul.Adapters.P6ByteReferenceReads

/-! A successful Source memory-byte write and the actual bounded MSTORE8 frame
update share one exact byte/string writeback. Entry representation, source index
bounds and physical fit are distinct. No source-local cleaning, allocator
provenance or general assembly/static-call adequacy is inferred. -/
namespace Solidity.Yul.Adapters.P6ByteReferenceWrite
open Solidity.Yul.Views Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

/-- One physical byte write changes the observed payload by the real list.set. -/
theorem payload_set (m : ByteView) (base : Nat) (old : Roadmap.Bytes)
    (payload : readBytes m base old.length=old) (i : Nat) (b : UInt8) :
    readBytes (Environment.writeByte m (base+i) b) base old.length=old.set i b := by
  apply List.ext_getElem
  · simp only [readBytes,List.length_map,List.length_range,List.length_set]
  · intro j hj hk
    have hjold : j<old.length := by simpa only [List.length_set] using hk
    have oldAt : m (base+j)=old[j] := by
      have selected := congrArg (fun xs : List UInt8 => xs[j]?) payload
      simpa only [readBytes,List.getElem?_map,List.getElem?_range,hjold,if_true,
        Option.map_some,List.getElem?_eq_getElem hjold,Option.some.injEq] using selected
    simp only [readBytes,List.getElem_map,List.getElem_range,Environment.writeByte,List.getElem_set]
    by_cases equal : j=i
    · subst j;simp only [if_true]
    · rw [if_neg (by omega),if_neg (by omega)]
      exact oldAt

/-- Payload stores do not rewrite the real length header. -/
theorem header_same (m : ByteView) (base i : Nat) (b : UInt8) :
    mload (Environment.writeByte m (base+32+i) b) base=mload m base := by
  apply mload_congr
  intro k
  exact if_neg (by have bound:=k.isLt;omega)

/-- Use the numeric byte, not the left-aligned bytes1 word. -/
def byteWord (b : UInt8) : Environment.Word :=
  lenU b.toNat (by have h:=b.toNat_lt;omega)

theorem store_image {C : Contract} {Δ : Ctx} (μ : FrameMem C Δ)
    (offset : Environment.Word) (b : UInt8) (fits : offset.val.toNat+1≤μ.capacity) :
    frameBytes (P6ByteMemory.store8 μ offset (byteWord b) fits)=
      Environment.writeByte (frameBytes μ) offset.val.toNat b := by
  unfold P6ByteMemory.store8
  rw [P6ByteMemory.write_image]
  change Environment.writeBytes (frameBytes μ) offset.val.toNat [UInt8.ofNat b.toNat]=_
  rw [UInt8.ofNat_toNat]
  rfl

/-- The placement and actual logical index derive a nonwrapping payload address. -/
def payloadOffset {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : h.get root=some ⟨heapByteType string,heapByteData D string old⟩)
    (i : Nat) (inside : i<old.length) : Environment.Word :=
  lenU (p.address root+32+i) (by
    have present : (h.cells root).isSome := by change (h.get root).isSome=true;rw [found];rfl
    have ends := p.ends root present
    rw [heapByte_placement_shape h p root string old found] at ends
    have live := byte_shape_live_bound old.length
    have bound := p.free.isLt
    omega)

/-- Exact physical writeback agrees with the ACTUAL successful Source byte
write, including the whole administrative store. Entry header/payload facts
are prestate representation, not an assumed output law. -/
theorem write {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (μ : FrameMem C Δ)
    (header : (mload (frameBytes μ) (p.address root)).val=old.length)
    (payload : readBytes (frameBytes μ) (p.address root+32) old.length=old)
    (i : Nat) (inside : i<old.length) (b : UInt8)
    (fits : p.address root+32+i+1≤μ.capacity) :
    let offset := payloadOffset p root string old found i inside
    let reached := P6ByteMemory.store8 μ offset (byteWord b) fits
    let out := withSourceHeap s (s.2.heap.write root
      (heapByteData E.layout string (old.set i b)) (heap_ty_of_get s.2.heap root _ _ found))
    (Source.writeLoc F n (.memByte root i) (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)).run s=
      (.ok (),out) ∧
    heapByteStateWriteback s p root string old found (frameBytes reached)=some out ∧
    bytesObjectView (old.set i b) (by rw [List.length_set];exact heapByte_length_bound s.2.heap p root string old found)
      (frameBytes reached) (p.address root)=frameBytes reached ∧
    (∀ H,Source.MemOK E H s → Source.MemOK E H out) ∧
    (∀ a,a≠root → out.2.heap.get a=s.2.heap.get a) ∧
    (∀ a,a≠p.address root+32+i → frameBytes reached a=frameBytes μ a) := by
  dsimp only
  have physical := store_image μ (payloadOffset p root string old found i inside) b fits
  change frameBytes (P6ByteMemory.store8 μ (payloadOffset p root string old found i inside) (byteWord b) fits)=
    Environment.writeByte (frameBytes μ) (p.address root+32+i) b at physical
  have newHeader : (mload (frameBytes (P6ByteMemory.store8 μ (payloadOffset p root string old found i inside) (byteWord b) fits)) (p.address root)).val=old.length := by
    rw [physical,header_same,header]
  have newPayload : readBytes (frameBytes (P6ByteMemory.store8 μ (payloadOffset p root string old found i inside) (byteWord b) fits))
      (p.address root+32) old.length=old.set i b := by
    rw [physical];exact payload_set _ _ _ payload i b
  refine ⟨P6ByteReferenceReads.write_byte F n s root string old found i inside b,?_,?_,?_,?_,?_⟩
  · unfold heapByteStateWriteback heapByteWriteback
    rw [newHeader,if_pos rfl,decodeHeapByte_data,newHeader,newPayload]
    rfl
  · apply bytesObject_unchanged
    · apply Fin.ext
      simpa only [List.length_set] using newHeader
    · intro j hj
      have hjold : j<old.length := by simpa only [List.length_set] using hj
      have read := congrArg (fun xs : List UInt8 => xs[j]?) newPayload
      simpa only [readBytes,List.getElem?_map,List.getElem?_range,hjold,if_true,
        Option.map_some,List.getElem?_eq_getElem hj,Option.some.injEq] using read.symm
  · intro H ok
    exact heapByte_write_MemOK E H s root string _ _ ok
  · intro a different
    exact Source.Heap.write_other s.2.heap different _ (heap_ty_of_get s.2.heap root _ _ found)
  · intro a different
    rw [physical]
    exact if_neg different

/-- The concrete mixed encoding supplies the entry facts; consumers need not
postulate a selected object's read agreement. -/
theorem mixed_entry {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (coverage : CoversMixedHeap es) (residual : ByteView)
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : h.get root=some ⟨heapByteType string,heapByteData D string old⟩) :
    (mload (encodeMixedHeap p es residual) (p.address root)).val=old.length ∧
    readBytes (encodeMixedHeap p es residual) (p.address root+32) old.length=old := by
  have bound := heapByte_length_bound h p root string old found
  have header : ObjectWord p.address (heapByteData D string old) 0 ⟨old.length,bound⟩ := by
    cases string
    · exact .bytesLength old bound
    · exact .stringLength old bound
  constructor
  · have exactHeader := encodeMixedHeap_source_word p es distinct coverage residual root _ _ found 0 _ header
    simpa only [Nat.add_zero] using congrArg Fin.val exactHeader
  · apply List.ext_getElem
    · simp only [readBytes,List.length_map,List.length_range]
    · intro j hj hjold
      simp only [readBytes,List.getElem_map,List.getElem_range]
      have byte : ObjectByte (heapByteData D string old) (32+j) old[j] := by
        cases string
        · exact .bytes old ⟨j,hjold⟩
        · exact .string old ⟨j,hjold⟩
      simpa only [Nat.add_assoc] using
        encodeMixedHeap_source_byte p es distinct coverage residual root _ _ found (32+j) old[j] byte

/-- Writing the unchanged byte preserves the WHOLE Source state and physical
byte map. The frame may still record access accounting. -/
theorem unchanged {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (μ : FrameMem C Δ)
    (payload : readBytes (frameBytes μ) (p.address root+32) old.length=old)
    (i : Nat) (inside : i<old.length) (fits : p.address root+32+i+1≤μ.capacity) :
    (Source.writeLoc F n (.memByte root i)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [old[i]] rfl)).run s=(.ok (),s) ∧
    frameBytes (P6ByteMemory.store8 μ (payloadOffset p root string old found i inside) (byteWord old[i]) fits)=
      frameBytes μ := by
  constructor
  · have run := P6ByteReferenceReads.write_byte F n s root string old found i inside old[i]
    simpa only [List.set_getElem_self inside,heap_write_unchanged s.2.heap root _ _ found,
      withSourceHeap_unchanged] using run
  · rw [store_image]
    have selected := congrArg (fun xs : List UInt8 => xs[i]?) payload
    have atByte : frameBytes μ (p.address root+32+i)=old[i] := by
      simpa only [readBytes,List.getElem?_map,List.getElem?_range,inside,if_true,
        Option.map_some,List.getElem?_eq_getElem inside,Option.some.injEq] using selected
    change Environment.writeByte (frameBytes μ) (p.address root+32+i) old[i]=frameBytes μ
    funext a
    unfold Environment.writeByte
    by_cases same : a=p.address root+32+i
    · rw [if_pos same,same];exact atByte.symm
    · exact if_neg same
end Solidity.Yul.Adapters.P6ByteReferenceWrite
