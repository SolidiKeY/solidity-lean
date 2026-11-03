import Solidity.Yul.Adapters.ComputedFrameHeap
import Solidity.Source.Semantics

/-! Actual Source allocations feed computed placement and complete frame
roundtrip. This witnesses the preparation, not general allocator refinement. -/
namespace Solidity.Yul.Adapters.ComputedFrameHeap.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
private def E : Source.Env := ⟨[]⟩
private def initial : Source.EMState E [] := (.nil,Source.St.init E)
private def bytes : Source.Data E.layout (.bytes .memory) := .bytes [1,255]
private def text : Source.Data E.layout (.string .memory) := .string [255,0]
private def first : Source.EMState E [] := ((Source.allocRef bytes).run initial).2
private def state : Source.EMState E [] := ((Source.allocRef text).run first).2
private theorem actual_MemOK : Source.MemOK E state.2.heap.ty state := by
  have start : Source.MemOK E initial.2.heap.ty initial :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have one := Source.allocRef_mem' (E:=E) (Γ:=[]) (H:=initial.2.heap.ty) bytes trivial trivial initial ⟨start,.bytes _⟩
  have firstOK : Source.MemOK E initial.2.heap.ty first := one.1
  have two := Source.allocRef_mem' (E:=E) (Γ:=[]) (H:=initial.2.heap.ty) text trivial trivial first ⟨firstOK,.string _⟩
  exact two.1.self
private theorem supported (a : Nat) (τ : Source.STy) (d : Source.Data E.layout τ)
    (found : state.2.heap.get a=some ⟨τ,d⟩) : InventoryTypeSupported E τ := by
  have bound : a<2 := by
    by_cases small : a<2
    · exact small
    · have no := state.2.heap.bounded a (show state.2.heap.next≤a by change 2≤a;omega)
      change state.2.heap.cells a=some ⟨τ,d⟩ at found
      rw [no] at found
      cases found
  have casesA : a=0 ∨ a=1 := by omega
  rcases casesA with rfl | rfl <;> cases found <;> trivial
private def C : Contract := {vars:=[]}
private def carrier (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨19,1,p,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=320,aligned:=⟨10,rfl⟩,data:=fun _=>0,highWaterWords:=10,
   resident:=by decide,zeroAbove:=by intro i hi;have bound:=i.isLt;omega}
private def residual : ByteView := mstore (fun k=>if k=319 then 170 else 0) 64 256
private theorem fits (p : Pipeline) : MemoryAgreement.Fits (carrier p) residual := by
  intro k high
  change 320≤k at high
  rw [residual,mstore_outside _ _ _ _ (by omega)]
  exact if_neg (by omega)

theorem computed_roundtrip (pipeline : Pipeline) :
    ∃ (p : Placement state.2.heap) (image : FrameMem C []),
      prepare state (carrier pipeline) residual (fits pipeline)=.ok ⟨p,image⟩ ∧
      enumeratedMemoryWriteback state p p (retainInitial _ _) (frameBytes image)=.ok (some (.ok (),state)) := by
  obtain ⟨p,image,prepared,coverage,distinct,raw,run,metadata⟩ := owner_roundtrip state.2.heap.ty state
    actual_MemOK supported rfl (by decide) (carrier pipeline) residual (fits pipeline) (by change 256≤320;decide)
  exact ⟨p,image,prepared,run⟩

private def observed (pipeline : Pipeline) : List Nat :=
  match prepare state (carrier pipeline) residual (fits pipeline) with
  | .error _=>[]
  | .ok ⟨p,image⟩=>
    match enumeratedMemoryWriteback state p p (retainInitial _ _) (frameBytes image) with
    | .ok (some (.ok (),out))=>
      let b := ((Source.heapBytes (E:=E) (Γ:=[]) 0).run out).1.toOption.getD []
      let s := ((Source.heapBytes (E:=E) (Γ:=[]) 1).run out).1.toOption.getD []
      [p.address 0,p.address 1,p.free.val]++b.map UInt8.toNat++s.map UInt8.toNat++[(frameBytes image 319).toNat]
    | _=>[]
/-- info: [128, 192, 256, 1, 255, 255, 0, 170] -/
#guard_msgs in #eval observed .legacy
/-- info: [128, 192, 256, 1, 255, 255, 0, 170] -/
#guard_msgs in #eval observed .viaIR
/-- info: false -/
#guard_msgs in #eval observed .viaIR==[128,128,256,1,255,255,0,0]
/-- Success itself supplies the computed guard facts; the actual incoming
reserved words are preserved without byte normalization. -/
theorem reserved_roundtrip (pipeline : Pipeline) :
    ∃ (p : Placement state.2.heap) (image : FrameMem C []),
      prepare state (carrier pipeline) residual (fits pipeline)=.ok ⟨p,image⟩ ∧
      ReservedOK (frameBytes image) p.free ∧
      enumeratedMemoryWriteback state p p (retainInitial _ _) (frameBytes image)=.ok (some (.ok (),state)) := by
  obtain ⟨p,image,done,run⟩ := computed_roundtrip pipeline
  obtain ⟨room,framed,placed⟩ := prepare_facts state (carrier pipeline) residual (fits pipeline) p image done
  have choices := ComputedPlacement.prepare_choices state.2.heap p placed
  have free : p.free.val=256 := choices.2.2.1
  have reserved : ReservedOK residual p.free := by
    constructor
    · rw [free]
      exact congrArg Fin.val (mload_mstore (fun k=>if k=319 then 170 else 0) 64 256)
    · intro i
      rw [residual,mstore_outside _ _ _ _ (by have hi:=i.isLt;omega)]
      exact if_neg (by have hi:=i.isLt;omega)
  exact ⟨p,image,done,prepare_reserved state (carrier pipeline) residual (fits pipeline) p image done reserved,run⟩

private def small (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=(carrier pipeline).key,scalar:=by intro R i;cases i
   capacity:=224,aligned:=⟨7,rfl⟩,data:=fun _=>0,highWaterWords:=7,
   resident:=by decide,zeroAbove:=by intro i high;have bound:=i.isLt;omega}

theorem insufficient_frame (pipeline : Pipeline) :
    prepare state (small pipeline) (fun _=>0) (fun _ _=>rfl)=.error (.frameRoom 256 224) := by
  let p := ComputedPlacement.build state.2.heap rfl (by decide)
  have placed : ComputedPlacement.prepare state.2.heap=.ok p :=
    ComputedPlacement.prepare_success _ _ _
  unfold prepare
  rw [placed]
  dsimp only
  rw [dif_neg (show ¬p.free.val≤(small pipeline).highWaterWords*32 by change ¬256≤224;decide)]
  rfl

private def dangling : Source.EMState E [] :=
  (.nil,{Source.St.init E with heap:=((Source.Heap.empty : Source.Heap E.layout).alloc
    ⟨.array .memory (.bytes .memory) none,.array 1 (fun _ h=>nomatch h)
      (fun _=>.val (.memRef rfl 7))⟩).1})

theorem unsupported_child (pipeline : Pipeline) :
    prepare dangling (carrier pipeline) (fun _=>0) (fun _ _=>rfl)=.error (.objects [0]) := rfl

/-- info: (256, 0, 170) -/
#guard_msgs in #eval
  match prepare state (carrier .legacy) residual (fits .legacy) with
  | .ok ⟨_p,image⟩ => ((mload (frameBytes image) 64).val,(mload (frameBytes image) 96).val,
      (frameBytes image 319).toNat)
  | _ => (0,0,0)
/-- info: false -/
#guard_msgs in #eval
  match prepare state (small .viaIR) (fun _=>0) (fun _ _=>rfl) with
  | .ok _ => true
  | _ => false

private def nonzeroReserved : ByteView := mstore residual 96 7
private theorem nonzeroFits (pipeline : Pipeline) : MemoryAgreement.Fits (carrier pipeline) nonzeroReserved := by
  intro k high
  change 320≤k at high
  rw [nonzeroReserved,mstore_outside _ _ _ _ (by omega)]
  exact fits pipeline k high
/-- info: 7 -/
#guard_msgs in #eval
  match prepare state (carrier .viaIR) nonzeroReserved (nonzeroFits .viaIR) with
  | .ok ⟨_p,image⟩ => (mload (frameBytes image) 96).val
  | _ => 999

/-- Original ObjectWord/ObjectByte observations from the actual successful
computed result, with no supplied coordinates, image inventory or read law. -/
theorem computed_reads (pipeline : Pipeline) :
    ∃ (p : Placement state.2.heap) (image : FrameMem C []),
      prepare state (carrier pipeline) residual (fits pipeline)=.ok ⟨p,image⟩ ∧
      mload (frameBytes image) (p.address 0)=2 ∧
      frameBytes image (p.address 0+32)=1 ∧ frameBytes image (p.address 0+33)=255 ∧
      mload (frameBytes image) (p.address 1)=2 ∧ frameBytes image (p.address 1+32)=255 := by
  obtain ⟨p,image,done,run⟩ := computed_roundtrip pipeline
  refine ⟨p,image,done,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.add_zero] using
      prepare_word state (carrier pipeline) residual (fits pipeline) p image done
        0 (.bytes .memory) bytes rfl 0 2 (.bytesLength _ (by decide))
  · exact prepare_byte state (carrier pipeline) residual (fits pipeline) p image done
      0 (.bytes .memory) bytes rfl 32 1 (.bytes _ ⟨0,by decide⟩)
  · exact prepare_byte state (carrier pipeline) residual (fits pipeline) p image done
      0 (.bytes .memory) bytes rfl 33 255 (.bytes _ ⟨1,by decide⟩)
  · simpa only [Nat.add_zero] using
      prepare_word state (carrier pipeline) residual (fits pipeline) p image done
        1 (.string .memory) text rfl 0 2 (.stringLength _ (by decide))
  · exact prepare_byte state (carrier pipeline) residual (fits pipeline) p image done
      1 (.string .memory) text rfl 32 255 (.string _ ⟨0,by decide⟩)

/-- The scratch/reserved preservation theorem does not clean a bad zero-word. -/
theorem reserved_byte_retained (pipeline : Pipeline) (p : Placement state.2.heap) (image : FrameMem C [])
    (done : prepare state (carrier pipeline) nonzeroReserved (nonzeroFits pipeline)=.ok ⟨p,image⟩) :
    frameBytes image 127=7 := by
  rw [prepare_prefix state (carrier pipeline) nonzeroReserved (nonzeroFits pipeline) p image done 127 (by decide)]
  rfl

/-- info: false -/
#guard_msgs in #eval
  match prepare state (carrier .viaIR) residual (fits .viaIR) with
  | .ok ⟨p,image⟩ => (mload (frameBytes image) (p.address 0+32)).val==2
  | _ => true

end Solidity.Yul.Adapters.ComputedFrameHeap.Controls
