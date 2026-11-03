import Solidity.Yul.Adapters.ObjectWriteback
import Solidity.Yul.Adapters.MemoryAgreement
import Solidity.Yul.Views.ByteObjects

/-! Consume the exact original byte/string physical codec and actual owner
heapPut. This does not infer object allocation ownership from frame capacity. -/
namespace Solidity.Yul.Adapters.PhysicalObject
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
variable {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}

def payload (m : ByteView) (base : Nat) : List UInt8 :=
  readBytes m (base+32) (mload m base).val

theorem payload_length (m : ByteView) (base : Nat) :
    (payload m base).length=(mload m base).val := by
  simp only [payload,readBytes,List.length_map,List.length_range]

theorem payload_bound (m : ByteView) (base : Nat) : (payload m base).length<2^256 := by
  rw [payload_length]
  exact (mload m base).isLt

/-- A real frame-span fact, not allocator provenance or a new decoding cap. -/
def Within (μ : FrameMem C Δ) (base : Nat) : Prop :=
  base+32+(mload (frameBytes μ) base).val≤μ.capacity

def packet (D : Source.Layout) (text : Bool) (m : ByteView) (base : Nat) : Σ τ, Source.Data D τ :=
  if text then ⟨.string .memory,decodeStringObject D m base⟩
  else ⟨.bytes .memory,decodeBytesObject D m base⟩

theorem prepared (y : Source.EMState E Γ) (text : Bool) (m : ByteView) (base : Nat) :
    ObjectWriteback.Prepared y (packet E.layout text m base) := by
  cases text
  · exact ⟨.bytes _,trivial,trivial⟩
  · exact ⟨.string _,trivial,trivial⟩

/-- Reconstruct from decoded header/payload while retaining the SAME arbitrary
raw map as complement. Derive complete map identity, including all padding. -/
theorem reconstruct (m : ByteView) (base : Nat) :
    bytesObjectView (payload m base) (payload_bound m base) m base=m := by
  apply bytesObject_unchanged
  · apply Fin.ext
    exact (payload_length m base).symm
  · intro i hi
    simp only [payload,readBytes,List.getElem_map,List.getElem_range]

/-- Decode-after-encode uses the original concrete codec laws, not a supplied
inverse field. All payload bytes, including nonUTF8 and noncanonical scalar
patterns, remain raw bytes. -/
theorem packet_encode (D : Source.Layout) (text : Bool) (bs : List UInt8) (bound : bs.length<2^256)
    (residual : ByteView) (base : Nat) :
    packet D text (bytesObjectView bs bound residual base) base=
      (if text then ⟨.string .memory,.string bs⟩ else ⟨.bytes .memory,.bytes bs⟩) := by
  cases text
  · simp only [packet,Bool.false_eq_true,if_false,decode_bytesObjectView]
  · simp only [packet,↓reduceIte,decode_stringObjectView]

def commit (μ : FrameMem C Δ) (text : Bool) (address base : Nat) : Source.EM E Γ Unit :=
  Source.heapPut address (packet E.layout text (frameBytes μ) base)

/-- Actual Source commit, exact selected data, all unrelated cells, complete
raw reconstruction and every original-H owner MemOK. Allocation/source-Yul
adequacy is separate; Within alone does not prove object ownership. -/
theorem commit_agreement (μ : FrameMem C Δ) (text : Bool) (address base : Nat)
    (y : Source.EMState E Γ)
    (typed : y.2.heap.ty address=some (packet E.layout text (frameBytes μ) base).1) :
    ∃ z, (commit μ text address base).run y=(.ok (),z) ∧
      z.2.heap.get address=some (packet E.layout text (frameBytes μ) base) ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ H : Source.HeapTy, Source.MemOK E H y → Source.MemOK E H z) ∧
      bytesObjectView (payload (frameBytes μ) base) (payload_bound _ _) (frameBytes μ) base=frameBytes μ ∧
      z.2.heap.ty=y.2.heap.ty ∧ z.2.heap.next=y.2.heap.next ∧ z.1=y.1 ∧
      z.2={y.2 with heap:=z.2.heap} := by
  obtain ⟨z,run,found,other,types,next,locals,state⟩:=ObjectWriteback.writeback y address
    (packet E.layout text (frameBytes μ) base) typed
  refine ⟨z,run,found,other,?_,reconstruct _ _,types,next,locals,state⟩
  intro H ok
  have h:=ObjectWriteback.memOK y address (packet E.layout text (frameBytes μ) base)
    (prepared y text _ _) H ok
  rw [run] at h
  exact h

theorem unchanged_source (μ : FrameMem C Δ) (text : Bool) (address base : Nat)
    (y : Source.EMState E Γ)
    (found : y.2.heap.get address=some (packet E.layout text (frameBytes μ) base)) :
    (commit μ text address base).run y=(.ok (),y) := ObjectWriteback.unchanged y address _ found

/-- The reconstructed view preserves the COMPLETE P6 frame, not just bytes. -/
theorem unchanged_frame (μ : FrameMem C Δ) (base : Nat) :
    MemoryAgreement.writeback μ
      (bytesObjectView (payload (frameBytes μ) base) (payload_bound _ _) (frameBytes μ) base)
      (by rw [reconstruct];exact MemoryAgreement.fits_view μ)=μ := by
  apply MemoryAgreement.unchanged
  exact reconstruct _ _
/-- Existing typed owner requests computed from ONE raw snapshot; no assumed
per-object inverse or final coverage law is supplied. -/
def packets (μ : FrameMem C Δ) (specs : List (Bool × Nat × Nat)) : List (ObjectWriteback.Request E) :=
  specs.map fun spec=>(spec.2.1,packet E.layout spec.1 (frameBytes μ) spec.2.2)

theorem commit_many (μ : FrameMem C Δ) (specs : List (Bool × Nat × Nat))
    (y : Source.EMState E Γ)
    (typed : ∀ spec∈specs,y.2.heap.ty spec.2.1=some (packet E.layout spec.1 (frameBytes μ) spec.2.2).1) :
    ∃ z, (ObjectWriteback.putAll (packets μ specs)).run y=(.ok (),z) ∧
      z.2.heap.ty=y.2.heap.ty ∧ z.2.heap.next=y.2.heap.next ∧ z.1=y.1 ∧
      z.2={y.2 with heap:=z.2.heap} ∧
      (∀ b,(∀ spec∈specs,b≠spec.2.1) → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ H : Source.HeapTy,Source.MemOK E H y → Source.MemOK E H z) := by
  have ready : ∀ request∈packets (E:=E) μ specs,
      y.2.heap.ty request.1=some request.2.1 ∧ ObjectWriteback.Prepared y request.2 := by
    intro request member
    obtain ⟨spec,hs,eq⟩:=List.mem_map.mp member
    subst request
    exact ⟨typed spec hs,prepared y spec.1 _ _⟩
  obtain ⟨z,run,types,next,locals,state,other,mem⟩:=ObjectWriteback.all_types y (packets μ specs) ready
  refine ⟨z,run,types,next,locals,state,?_,mem⟩
  intro b outside
  apply other
  intro request member
  obtain ⟨spec,hs,eq⟩:=List.mem_map.mp member
  subst request
  exact outside spec hs

theorem unchanged_many (μ : FrameMem C Δ) (specs : List (Bool × Nat × Nat))
    (y : Source.EMState E Γ)
    (found : ∀ spec∈specs,y.2.heap.get spec.2.1=some (packet E.layout spec.1 (frameBytes μ) spec.2.2)) :
    (ObjectWriteback.putAll (packets μ specs)).run y=(.ok (),y) := by
  apply ObjectWriteback.all_unchanged
  intro request member
  obtain ⟨spec,hs,eq⟩:=List.mem_map.mp member
  subst request
  exact found spec hs
/-- Decode one actual raw snapshot into dependent byte/string packets and
execute through the first actual Source type error. The packet codecs derive
all owner data invariants; no type-success or final-view law is supplied.
Raw reconstruction retains all residual bytes. Allocation ownership and
physical Within remain separate from this canonical snapshot preparation. -/
theorem commit_many_checked {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (μ : FrameMem C Δ) (specs : List (Bool × Nat × Nat)) (y : Source.EMState E Γ) :
    let requests := packets (E:=E) μ specs
    let good := fun request : ObjectWriteback.Request E=>decide (y.2.heap.ty request.1=some request.2.1)
    let accepted := requests.takeWhile good
    ∃ z, (ObjectWriteback.putAll accepted).run y=(.ok (),z) ∧
      (ObjectWriteback.putAll requests).run y=
        ((if (requests.dropWhile good).isEmpty then .ok () else .error (.stuck "memory write type")),z) ∧
      z.2.heap.ty=y.2.heap.ty ∧ z.2.heap.next=y.2.heap.next ∧ z.1=y.1 ∧
      z.2={y.2 with heap:=z.2.heap} ∧
      (∀ b,(∀ request∈accepted,b≠request.1) → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ H : Source.HeapTy,Source.MemOK E H y → Source.MemOK E H z) ∧
      (∀ spec∈specs,Solidity.Yul.Views.bytesObjectView (payload (frameBytes μ) spec.2.2)
        (payload_bound _ _) (frameBytes μ) spec.2.2=frameBytes μ) := by
  dsimp only
  have ready : ∀ request∈(packets (E:=E) μ specs).takeWhile
      (fun request=>decide (y.2.heap.ty request.1=some request.2.1)),
      ObjectWriteback.Prepared y request.2 := by
    intro request member
    have memberAll : request∈packets (E:=E) μ specs := List.takeWhile_subset _ member
    obtain ⟨spec,hs,eq⟩ := List.mem_map.mp memberAll
    subst request
    exact prepared y spec.1 _ _
  obtain ⟨z,run,complete,types,next,locals,state,other,mem⟩ :=
    ObjectWriteback.all_types_checked y (packets μ specs) ready
  exact ⟨z,run,complete,types,next,locals,state,other,mem,fun spec _=>reconstruct _ _⟩

end Solidity.Yul.Adapters.PhysicalObject
