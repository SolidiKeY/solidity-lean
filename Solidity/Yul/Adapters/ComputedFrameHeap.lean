import Solidity.Yul.Views.ComputedPlacement
import Solidity.Yul.Adapters.FrameHeap

/-! Checked geometric preparation followed by the existing complete canonical
heap-image preparation. This supplies a mathematical placement and frame, not
reachable allocation provenance or compiler refinement. All three preparation
failure stages remain explicit and are not Source/Yul execution verdicts. -/
namespace Solidity.Yul.Adapters.ComputedFrameHeap
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
variable {E : Source.Env} {Ξ : Source.RCtx} {C : Contract} {Γ : Ctx}

inductive Error where
  | placement (reason : ComputedPlacement.Error)
  | frameRoom (computedEnd availableBytes : Nat)
  | objects (unsupportedIds : List Nat)
  deriving DecidableEq, Repr

def prepare (s : Source.EMState E Ξ) (carrier : FrameMem C Γ) (residual : ByteView)
    (fits : MemoryAgreement.Fits carrier residual) :
    Except Error (Σ _p : Placement s.2.heap,FrameMem C Γ) :=
  match ComputedPlacement.prepare s.2.heap with
  | .error reason=>.error (.placement reason)
  | .ok p=>
    if room : p.free.val≤carrier.highWaterWords*32 then
      match FrameHeap.prepareFrame carrier p residual fits room with
      | .error ids=>.error (.objects ids)
      | .ok image=>.ok ⟨p,image⟩
    else .error (.frameRoom p.free.val (carrier.highWaterWords*32))

/-- Constructive complete Source roundtrip without supplied Placement or entry
inventory. Guards are the actual checked computations. The initial retained
certificate concerns this mathematical placement, not allocator reachability. -/
theorem owner_roundtrip {E : Source.Env} {Ξ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (H : Source.HeapTy) (s : Source.EMState E Ξ) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (clear : ComputedPlacement.unsupported s.2.heap=[])
    (bound : ComputedPlacement.position s.2.heap s.2.heap.next<2^256)
    (carrier : FrameMem C Γ) (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : ComputedPlacement.position s.2.heap s.2.heap.next≤carrier.highWaterWords*32) :
    ∃ (p : Placement s.2.heap) (image : FrameMem C Γ),
      prepare s carrier residual fits=.ok ⟨p,image⟩ ∧
      CoversMixedHeap (generatedHeapEntries p) ∧ ((generatedHeapEntries p).map MixedHeapEntry.id).Nodup ∧
      frameBytes image=encodeMixedHeap p (generatedHeapEntries p) residual ∧
      enumeratedMemoryWriteback s p p (retainInitial _ _) (frameBytes image)=.ok (some (.ok (),s)) ∧
      image.st=carrier.st ∧ image.key=carrier.key ∧ image.capacity=carrier.capacity ∧
      image.highWaterWords=carrier.highWaterWords := by
  let p := ComputedPlacement.build s.2.heap clear bound
  have roomP : p.free.val≤carrier.highWaterWords*32 := room
  obtain ⟨image,frame,coverage,distinct,bytes,run,state,key,capacity,high⟩ :=
    FrameHeap.owner_roundtrip H s p p (retainInitial _ _) ok supported carrier residual fits roomP
  refine ⟨p,image,?_,coverage,distinct,bytes,run,state,key,capacity,high⟩
  unfold prepare
  rw [ComputedPlacement.prepare_success s.2.heap clear bound]
  dsimp only
  rw [dif_pos roomP,frame]

/-- Successful checked results expose the ACTUAL placement/frame producers
and derived room fact, not caller-supplied guard or final-view laws. -/
theorem prepare_facts {E : Source.Env} {Ξ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (s : Source.EMState E Ξ) (carrier : FrameMem C Γ) (residual : ByteView)
    (fits : MemoryAgreement.Fits carrier residual) (p : Placement s.2.heap) (image : FrameMem C Γ)
    (done : prepare s carrier residual fits=.ok ⟨p,image⟩) :
    ∃ room : p.free.val≤carrier.highWaterWords*32,
      FrameHeap.prepareFrame carrier p residual fits room=.ok image ∧
      ComputedPlacement.prepare s.2.heap=.ok p := by
  unfold prepare at done
  cases placed : ComputedPlacement.prepare s.2.heap with
  | error reason => rw [placed] at done;cases done
  | ok q =>
    rw [placed] at done
    dsimp only at done
    by_cases room : q.free.val≤carrier.highWaterWords*32
    · rw [dif_pos room] at done
      cases framed : FrameHeap.prepareFrame carrier q residual fits room with
      | error ids => rw [framed] at done;cases done
      | ok made =>
        rw [framed] at done
        have pair : (⟨q,made⟩ : Σ _p : Placement s.2.heap,FrameMem C Γ)=⟨p,image⟩ := Except.ok.inj done
        have same := congrArg (fun result : Σ _p : Placement s.2.heap,FrameMem C Γ=>result.1) pair
        cases same
        have sameImage := congrArg (fun result : Σ _p : Placement s.2.heap,FrameMem C Γ=>result.2) pair
        cases sameImage
        exact ⟨room,framed,rfl⟩
    · rw [dif_neg room] at done
      cases done

/-- Soundness from ANY successful preparation. All computational guards are
recovered from the result; original owner MemOK/type support remain explicit. -/
theorem prepare_sound (H : Source.HeapTy) (s : Source.EMState E Ξ) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (carrier : FrameMem C Γ) (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (p : Placement s.2.heap) (image : FrameMem C Γ) (done : prepare s carrier residual fits=.ok ⟨p,image⟩) :
    CoversMixedHeap (generatedHeapEntries p) ∧ ((generatedHeapEntries p).map MixedHeapEntry.id).Nodup ∧
      frameBytes image=encodeMixedHeap p (generatedHeapEntries p) residual ∧
      enumeratedMemoryWriteback s p p (retainInitial _ _) (frameBytes image)=.ok (some (.ok (),s)) ∧
      image.st=carrier.st ∧ image.key=carrier.key ∧ image.capacity=carrier.capacity ∧
      image.highWaterWords=carrier.highWaterWords := by
  obtain ⟨room,framed,placed⟩ := prepare_facts s carrier residual fits p image done
  obtain ⟨made,frame,coverage,distinct,bytes,run,state,key,capacity,high⟩ :=
    FrameHeap.owner_roundtrip H s p p (retainInitial _ _) ok supported carrier residual fits room
  have same : made=image := Except.ok.inj (frame.symm.trans framed)
  cases same
  exact ⟨coverage,distinct,bytes,run,state,key,capacity,high⟩

/-- Reserved-word agreement is transported from REAL input bytes, never
installed by cleaning. It needs no owner MemOK or decoder inverse premise. -/
theorem prepare_reserved (s : Source.EMState E Ξ) (carrier : FrameMem C Γ)
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (p : Placement s.2.heap) (image : FrameMem C Γ) (done : prepare s carrier residual fits=.ok ⟨p,image⟩)
    (reserved : ReservedOK residual p.free) : ReservedOK (frameBytes image) p.free := by
  obtain ⟨room,framed,placed⟩ := prepare_facts s carrier residual fits p image done
  unfold FrameHeap.prepareFrame at framed
  cases inventory : prepareHeapInventory p with
  | error ids => rw [inventory] at framed;cases framed
  | ok es =>
    rw [inventory] at framed
    change Except.ok (FrameHeap.frameOf carrier p es residual fits room)=Except.ok image at framed
    have same := Except.ok.inj framed
    rw [←same]
    exact FrameHeap.frame_reserved carrier p es residual fits room reserved

/-- Exact typed image and complete coverage follow from successful image
construction alone. No owner MemOK, canonical-decoder profile or final view
agreement is an input to this read-side result. -/
theorem prepare_image {E : Source.Env} {Ξ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (s : Source.EMState E Ξ) (carrier : FrameMem C Γ) (residual : ByteView)
    (fits : MemoryAgreement.Fits carrier residual) (p : Placement s.2.heap) (image : FrameMem C Γ)
    (done : prepare s carrier residual fits=.ok ⟨p,image⟩) :
    CoversMixedHeap (generatedHeapEntries p) ∧ ((generatedHeapEntries p).map MixedHeapEntry.id).Nodup ∧
      frameBytes image=encodeMixedHeap p (generatedHeapEntries p) residual := by
  obtain ⟨room,framed,placed⟩ := prepare_facts s carrier residual fits p image done
  unfold FrameHeap.prepareFrame at framed
  cases inventory : prepareHeapInventory p with
  | error ids => rw [inventory] at framed;cases framed
  | ok es =>
    have facts := prepareHeapInventory_ok p es inventory
    rw [inventory] at framed
    change Except.ok (FrameHeap.frameOf carrier p es residual fits room)=Except.ok image at framed
    have same := Except.ok.inj framed
    rw [←same,FrameHeap.frameOf_bytes,←facts.1]
    exact ⟨facts.2.1,facts.2.2,rfl⟩

theorem prepare_word (s : Source.EMState E Ξ) (carrier : FrameMem C Γ)
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (p : Placement s.2.heap) (image : FrameMem C Γ) (done : prepare s carrier residual fits=.ok ⟨p,image⟩)
    (a : Nat) (τ : Source.STy) (d : Source.Data E.layout τ) (found : s.2.heap.get a=some ⟨τ,d⟩)
    (off : Nat) (w : Roadmap.Word) (read : ObjectWord p.address d off w) :
    mload (frameBytes image) (p.address a+off)=w := by
  obtain ⟨coverage,distinct,raw⟩ := prepare_image s carrier residual fits p image done
  rw [raw]
  exact encodeMixedHeap_source_word p _ distinct coverage residual a τ d found off w read

theorem prepare_byte (s : Source.EMState E Ξ) (carrier : FrameMem C Γ)
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (p : Placement s.2.heap) (image : FrameMem C Γ) (done : prepare s carrier residual fits=.ok ⟨p,image⟩)
    (a : Nat) (τ : Source.STy) (d : Source.Data E.layout τ) (found : s.2.heap.get a=some ⟨τ,d⟩)
    (off : Nat) (v : UInt8) (read : ObjectByte d off v) :
    frameBytes image (p.address a+off)=v := by
  obtain ⟨coverage,distinct,raw⟩ := prepare_image s carrier residual fits p image done
  rw [raw]
  exact encodeMixedHeap_source_byte p _ distinct coverage residual a τ d found off v read

theorem prepare_residual (s : Source.EMState E Ξ) (carrier : FrameMem C Γ)
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (p : Placement s.2.heap) (image : FrameMem C Γ) (done : prepare s carrier residual fits=.ok ⟨p,image⟩)
    (k : Nat) (outside : ∀ e∈generatedHeapEntries p,k<p.address e.id ∨ p.address e.id+e.image.span≤k) :
    frameBytes image k=residual k := by
  rw [(prepare_image s carrier residual fits p image done).2.2]
  exact encodeMixedHeap_residual p _ residual k outside

/-- Scratch/reserved bytes are retained exactly, even if ReservedOK is absent.
This is preservation, never a claim that arbitrary reserved bytes are valid. -/
theorem prepare_prefix (s : Source.EMState E Ξ) (carrier : FrameMem C Γ)
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (p : Placement s.2.heap) (image : FrameMem C Γ) (done : prepare s carrier residual fits=.ok ⟨p,image⟩)
    (k : Nat) (low : k<128) : frameBytes image k=residual k := by
  apply prepare_residual s carrier residual fits p image done k
  intro e member
  have present : (s.2.heap.cells e.id).isSome := by
    change (s.2.heap.get e.id).isSome=true
    rw [e.found]
    rfl
  have start := p.starts e.id present
  exact Or.inl (by omega)

end Solidity.Yul.Adapters.ComputedFrameHeap
