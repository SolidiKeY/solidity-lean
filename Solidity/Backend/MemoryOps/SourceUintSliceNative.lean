import Solidity.Backend.MemoryOps.SourceCalldataSlice
import Solidity.Backend.MemoryOps.SourceGuardedUintDelete

/-! Existing actual uint slicing/copying connected to paired intrinsic allocation.
Only the public byte decoder and existing copy producer are composed here.
Prepared views/frames remain explicit; no ABI binder or target copy is added. -/
namespace Solidity.Backend.MemoryOps

/-- All bounds branches execute existing Source syntax. Successful payloads are
computed from bytes; uint decoding introduces no extra failure or oracle. -/
theorem source_uint_slice_raw_eval {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e) :
    (Source.evalE G F (fuel+3) (sourceUintSliceCopy root start finish toEnd)).run y=
      let stop := if toEnd then len else e.1.toNat
      if stop<s.1.toNat then (.error (.revert []),y)
      else if len<stop then (.error (.revert []),y)
      else (.ok (.val (.memRef rfl y.2.heap.next)),(y.1,{y.2 with heap :=
        (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory
          (CalldataPackets.RawUint.payload F (off+32*s.1.toNat) (stop-s.1.toNat))⟩).1})) := by
  first
  | solve | rfl | simp only [] | omega
  | simpa only [source_cd_uint_values_raw,source_uint_payload_sourceUint] using
      source_uint_slice_copy_eval G F fuel y root start finish off len s e toEnd hr hs he

/-- Actual slice syntax produces the SAME fresh object certified by the
existing paired copy producer. Old occupied Source objects/typed heaps and
valid-old-ID address agreement are derived, not postcondition premises. -/
theorem source_uint_slice_raw_native {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (address : Nat → Nat)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (capacity : (if toEnd then len else e.1.toNat)-s.1.toNat<2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)).length<2^256,
      let o : MObj H (.array (.prim .uint)) := ⟨CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat),valid⟩
      let pair := hp.alloc o
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory (CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat))⟩).1})
      (Source.evalE G F (fuel+3) (sourceUintSliceCopy root start finish toEnd)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      Heap.Keeps ext hp pair.1 ∧
      SourceUintMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      (∀ i,i<H.length → address' i=address i) ∧
      (∀ R (q : HRef H R),(q.wk ext).id≠pair.2.id) ∧
      (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
      (∀ R (q : HRef H R) (a : ArrTy R (.prim .uint)),
        SourceUintMemoryAt y (address q.id) hp q a →
        SourceUintMemoryAt z (address' (q.wk ext).id) pair.1 (q.wk ext) a) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | rfl | simp only [] | omega
  | rw [source_uint_slice_copy_window G F fuel y root start finish off len s e toEnd hr hs he ordered bounded]
    simpa only [source_cd_uint_values_raw,source_uint_payload_sourceUint] using
      source_cd_uint_copy y hp address F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat) capacity SH memOK


/-- A pure actual entry guard precedes the existing Source slice expression.
It validates the prepared input view; it does not manufacture argument locals. -/
def sourceGuardedUintSliceCopy {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish : Source.Idx Γ (.int .u256)) (toEnd : Bool)
    (data : List UInt8) (entry : Nat) : Source.EM E Γ (Source.RVal E.layout SourceUintArrayTy) :=
  Source.EM.lift (Source.cdTail data entry 32) >>= fun _ =>
    Source.evalE G F (fuel+3) (sourceUintSliceCopy root start finish toEnd)

/-- Byte-derived valid entry plus actual slice/copy and native allocation,
with explicit prepared-view and caller-frame binding premises. -/
theorem source_guarded_uint_slice_native {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (address : Nat → Nat)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish : Source.Idx Γ (.int .u256))
    (selector data : List UInt8) (four : selector.length=4) (binding : F.cd=selector++data)
    (entry : Nat) (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0))
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (small : (Source.wordAt (data.drop (Source.wordAt data entry)) 0)<2^64)
    (span : Source.wordAt data entry+32+32*(Source.wordAt (data.drop (Source.wordAt data entry)) 0)≤data.length)
    (ordered : s.1.toNat≤(if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)) (bounded : (if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)≤(Source.wordAt (data.drop (Source.wordAt data entry)) 0))
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    Source.cdTail data entry 32=.ok ((4+Source.wordAt data entry+32),(Source.wordAt (data.drop (Source.wordAt data entry)) 0)) ∧
    ∃ valid : (CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32+32*s.1.toNat) ((if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)-s.1.toNat)).length<2^256,
      let o : MObj H (.array (.prim .uint)) := ⟨CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32+32*s.1.toNat) ((if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)-s.1.toNat),valid⟩
      let pair := hp.alloc o
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory (CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32+32*s.1.toNat) ((if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)-s.1.toNat))⟩).1})
      (Source.evalE G F (fuel+3) (sourceUintSliceCopy root start finish toEnd)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      Heap.Keeps ext hp pair.1 ∧
      SourceUintMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      (∀ i,i<H.length → address' i=address i) ∧
      (∀ R (q : HRef H R),(q.wk ext).id≠pair.2.id) ∧
      (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
      (∀ R (q : HRef H R) (a : ArrTy R (.prim .uint)),
        SourceUintMemoryAt y (address q.id) hp q a →
        SourceUintMemoryAt z (address' (q.wk ext).id) pair.1 (q.wk ext) a) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧
      (sourceGuardedUintSliceCopy G F fuel root start finish toEnd data entry).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),z) := by
  first
  | solve | rfl | simp only [] | omega
  | have tail := source_uint_entry_tail data entry small span
    have capacity : (if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)-s.1.toNat<2^256 :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) bounded) (Nat.lt_trans small (by decide))
    have bytes : CalldataPackets.RawUint.payload F ((4+Source.wordAt data entry+32)+32*s.1.toNat) ((if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)-s.1.toNat)=
        CalldataPackets.RawUint.dataPayload data (Source.wordAt data entry+32+32*s.1.toNat) ((if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)-s.1.toNat) := by
      simpa only [Nat.add_assoc] using CalldataPackets.RawUint.payload_frame F selector data four binding
        (Source.wordAt data entry+32+32*s.1.toNat) ((if toEnd then (Source.wordAt (data.drop (Source.wordAt data entry)) 0) else e.1.toNat)-s.1.toNat)
    have copy := source_uint_slice_raw_native y hp address G F fuel root start finish (4+Source.wordAt data entry+32) (Source.wordAt (data.drop (Source.wordAt data entry)) 0)
      s e toEnd hr hs he ordered bounded capacity SH memOK
    rw [bytes] at copy
    obtain ⟨valid,run,keep,fresh,mok,identity,newAddress,oldMap,separate,preserved,aliases,locals,ex,events,logs,fn⟩ := copy
    refine ⟨tail,valid,run,keep,fresh,mok,identity,newAddress,oldMap,separate,preserved,aliases,locals,ex,events,logs,fn,?_⟩
    rw [sourceGuardedUintSliceCopy,tail]
    exact run

/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_raw_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_raw_eval
/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_raw_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_raw_native
/-- info: 'Solidity.Backend.MemoryOps.source_guarded_uint_slice_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_guarded_uint_slice_native
end Solidity.Backend.MemoryOps
