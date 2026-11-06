import Solidity.Backend.MemoryOps.PhysicalFrameImage
import Solidity.Backend.MemoryOps.PhysicalReferenceArray

/-! Scaled reference-pointer stores in the existing bounded scalar-frame SIDE
image. FrameMem.store32 preserves its carried intrinsic state; it does not
update that heap or admit incoming reference locals. An external typed heap
update and its word/byte observations are separate explicit conclusions. -/
namespace Solidity.Backend.MemoryOps.Physical
open Evm.TryByteImage

/-- Logical pointer words and scaled physical pointer bytes commute with the
existing typed frame store. Neither a new serializer nor a heap reindexing is
introduced; the frame's intrinsic state and full invocation key stay fixed. -/
theorem PointerFrame.frame_store {C : Contract} {Γ : Ctx}
    {μ : FrameMem C Γ} {m : Evm.Machine} {live : Nat → Prop}
    (h : PointerFrame m (frameBytes μ) live) (cell value : Fin Evm.W)
    (selected : live cell.val) (a : WordSpan μ.capacity)
    (aligned : a.offset.val.toNat=32*cell.val) (valueFits : 32*value.val<2^256)
    (tail : List Environment.Word) :
    let stored := store32 μ a (Evm.Memory.indexValue ⟨32*value.val,valueFits⟩)
    Evm.run [.mstoreAt] ((m.push (.val value)).push (.val cell))=
      .ok (Evm.Memory.writeMachine m cell.val (.val value)) 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨a.offset::Evm.Memory.indexValue ⟨32*value.val,valueFits⟩::tail,frameBytes μ⟩=
        some ⟨tail,frameBytes stored⟩ ∧
    PointerFrame (Evm.Memory.writeMachine m cell.val (.val value)) (frameBytes stored)
      (fun c => live c ∨ c=cell.val) ∧ stored.st=μ.st ∧ stored.key=μ.key := by
  dsimp only
  refine ⟨word_mstore m cell value,(frame_store32_target μ a (Evm.Memory.indexValue ⟨32*value.val,valueFits⟩) tail).1,?_,
    (store32_frame μ a _).1,(store32_frame μ a _).2⟩
  rw [frameBytes_store32,aligned]
  simp only [Evm.Memory.indexValue,Int.toNat_natCast]
  exact h.write cell.val value (h.fits cell.val selected) valueFits

/-- Actual typed reference-array store plus its full existing word program
and actual frame-image store. The new external heap is NOT asserted to be the
frame's carried heap: store32 leaves its original intrinsic state unchanged. -/
theorem ReferenceArrayAt.store_frame {C : Contract} {Γ : Ctx} {H : HTy} {R : RefTy}
    {hp : Heap H} {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} (μ : FrameMem C Γ)
    (h : ReferenceArrayAt hp root base m (frameBytes μ)) (i : Fin Evm.W)
    (hi : i.val<hp.len root .dyn) (child : HRef H R)
    (childFits : 32*(base child.id).val<2^256) (a : WordSpan μ.capacity)
    (aligned : a.offset.val.toNat=32*((base root.id).val+1+i.val)) (tail : List Environment.Word) :
    let cell := (base root.id).val+1+i.val
    let stored := store32 μ a (Evm.Memory.indexValue ⟨32*(base child.id).val,childFits⟩)
    ∃ out : Heap H,
      hp.writeAddr (.index root .dyn (Evm.Memory.indexValue i)) child=some out ∧
      Evm.run (Evm.Memory.writeArrayCode (base root.id))
        ((m.push (.val (base child.id))).push (.val i))=
          .ok (Evm.Memory.writeMachine m cell (.val (base child.id))) 0 ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨a.offset::Evm.Memory.indexValue ⟨32*(base child.id).val,childFits⟩::tail,frameBytes μ⟩=
          some ⟨tail,frameBytes stored⟩ ∧
      ReferenceArrayAt out root base (Evm.Memory.writeMachine m cell (.val (base child.id))) (frameBytes stored) ∧
      stored.st=μ.st ∧ stored.key=μ.key ∧
      (∀ {Q : RefTy} (q : HRef H Q),root.id≠q.id → out.get q=hp.get q) := by
  dsimp only
  have image : frameBytes (store32 μ a (Evm.Memory.indexValue ⟨32*(base child.id).val,childFits⟩))=
      Environment.writeBytes (frameBytes μ) (32*((base root.id).val+1+i.val)) (Semantics.wordBytes (32*(base child.id).val)) := by
    rw [frameBytes_store32,aligned]
    simp only [Evm.Memory.indexValue,Int.toNat_natCast]
  obtain ⟨out,ht,hw,_,hr,hobjects⟩ := h.store i hi child childFits
  refine ⟨out,ht,hw,(frame_store32_target μ a (Evm.Memory.indexValue ⟨32*(base child.id).val,childFits⟩) tail).1,?_,
    (store32_frame μ a _).1,(store32_frame μ a _).2,hobjects⟩
  rw [image]
  exact hr

/-- Existing scalar-frame typing excludes a live reference local. This is an
interface boundary, not a new exclusion of the Source or target language. -/
theorem frame_reference_local_impossible {C : Contract} {Γ : Ctx} {R : RefTy}
    (i : Idx Γ (.mem R)) : ¬ Nonempty (FrameMem C Γ) := by
  intro h
  obtain ⟨μ⟩ := h
  exact μ.scalar R i

/-- info: 'Solidity.Backend.MemoryOps.Physical.PointerFrame.frame_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PointerFrame.frame_store
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.store_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.store_frame
/-- info: 'Solidity.Backend.MemoryOps.Physical.frame_reference_local_impossible' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms frame_reference_local_impossible

end Solidity.Backend.MemoryOps.Physical
