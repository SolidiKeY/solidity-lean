import Solidity.Backend.MemoryOps.PhysicalByteJournal
import Solidity.Evm.TryByteImage

/-! Projection of the EXISTING typed invocation-frame byte image into the
EXISTING byte target memory. Store32 is reused, not reimplemented. Capacity,
invocation identity and carried intrinsic state are explicit; this does not
turn that side image into a Source heap, global transaction or gas model. -/
namespace Solidity.Backend.MemoryOps.Physical
open Evm.TryByteImage

/-- Existing bounded frame bytes, with the existing zero convention outside
the representation capacity. This is a projection, not a new state/evaluator. -/
def frameBytes {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ) : Environment.Memory :=
  fun k => if h : k<μ.capacity then μ.data ⟨k,h⟩ else 0

theorem frame_wordByte (w : PrimTy.uint.Denote) (j : Nat) (hj : j<32) :
    wordByte w j=(Semantics.wordBytes w.val.toNat)[j]'(by rw [word_bytes_length];exact hj) := by
  simp only [wordByte,Semantics.wordBytes,List.getElem_map,List.getElem_range]

/-- Complete commuting byte image, including unaligned stores and ALL exterior
bytes; a desired image equality is not an input. -/
theorem frameBytes_store32 {C : Contract} {Γ : Ctx}
    (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : PrimTy.uint.Denote) :
    frameBytes (store32 μ a w)=
      Environment.writeBytes (frameBytes μ) a.offset.val.toNat (Semantics.wordBytes w.val.toNat) := by
  funext k
  change (if h : k<μ.capacity then (store32 μ a w).data ⟨k,h⟩ else 0)=_
  have fits : a.offset.val.toNat+32≤μ.capacity := a.fits
  by_cases hk : k<μ.capacity
  · rw [dif_pos hk]
    by_cases inside : a.offset.val.toNat≤k ∧ k<a.offset.val.toNat+32
    · rw [store32_at μ a w ⟨k,hk⟩ inside]
      have hj : k-a.offset.val.toNat<32 := by omega
      have add : a.offset.val.toNat+(k-a.offset.val.toNat)=k := by omega
      have targetRead : Environment.writeBytes (frameBytes μ) a.offset.val.toNat
          (Semantics.wordBytes w.val.toNat) k=
          (Semantics.wordBytes w.val.toNat)[k-a.offset.val.toNat]'(by rw [word_bytes_length];exact hj) := by
        simpa only [add] using Environment.writeBytes_at (Semantics.wordBytes w.val.toNat)
          a.offset.val.toNat (k-a.offset.val.toNat) (frameBytes μ) (by rw [word_bytes_length];exact hj)
      exact (frame_wordByte w _ hj).trans targetRead.symm
    · rw [store32_outside μ a w ⟨k,hk⟩ inside]
      rw [Environment.writeBytes_frame _ _ _ _ (by rw [word_bytes_length];omega)]
      simp only [frameBytes,dif_pos hk]
  · rw [dif_neg hk]
    rw [Environment.writeBytes_frame _ _ _ _ (by rw [word_bytes_length];omega)]
    simp only [frameBytes,dif_neg hk]

/-- Actual published MSTORE consumes the frame's byte offset and value. The
reached memory is the projected EXISTING store32, with caller tail, carried
intrinsic state and full invocation key retained. -/
theorem frame_store32_target {C : Contract} {Γ : Ctx}
    (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : PrimTy.uint.Denote)
    (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE) ⟨a.offset::w::tail,frameBytes μ⟩=
      some ⟨tail,frameBytes (store32 μ a w)⟩ ∧
    (store32 μ a w).st=μ.st ∧ (store32 μ a w).key=μ.key := by
  refine ⟨?_,(store32_frame μ a w).1,(store32_frame μ a w).2⟩
  rw [frameBytes_store32]
  rfl

/-- The existing immutable typed-frame snapshot is exactly the target byte
reader on the same reached memory. Empty spans read nothing at any offset. -/
theorem frame_snapshot_read {C : Contract} {Γ : Ctx}
    (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) :
    snapshot μ s=Environment.readMemory (frameBytes μ) s.offset.val.toNat s.length.val.toNat := by
  apply List.ext_getElem
  · simp only [snapshot_length,Environment.readMemory,List.length_map,List.length_range]
  · intro j hj _
    have hi : j<s.length.val.toNat := by rw [snapshot_length] at hj;exact hj
    have fit : s.offset.val.toNat+j<μ.capacity := by
      rcases s.fits with hz | hz <;> omega
    rw [snapshot_get μ s j hj]
    simp only [Environment.readMemory,List.getElem_map,List.getElem_range]
    simp only [frameBytes,dif_pos fit]

/-- Reserving more zero-filled representation capacity changes no target byte.
This is the existing expandZero operation, not a gas/allocator realization. -/
theorem frameBytes_expandZero {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ) (n : Nat) :
    frameBytes (expandZero μ n)=frameBytes μ := by
  funext k
  change (if h : k<μ.capacity+n*32 then (expandZero μ n).data ⟨k,h⟩ else 0)=frameBytes μ k
  by_cases old : k<μ.capacity
  · rw [dif_pos (by omega),expandZero_old μ n ⟨k,old⟩]
    simp only [frameBytes,dif_pos old]
  · by_cases new : k<μ.capacity+n*32
    · rw [dif_pos new,expandZero_new μ n ⟨k,new⟩ (by change μ.capacity≤k;omega)]
      simp only [frameBytes,dif_neg old]
    · rw [dif_neg new]
      simp only [frameBytes,dif_neg old]

/-- For an aligned already represented cell, its INITIAL WordFrame supplies
physical W-fit (not merely frame-capacity fit). The existing frame store then
preserves the actual word/byte relation. No global pointer relocation follows. -/
theorem WordFrame.frame_store {C : Contract} {Γ : Ctx}
    {μ : FrameMem C Γ} {m : Evm.Machine} {live : Nat → Prop}
    (h : WordFrame m (frameBytes μ) live) (cell w : Fin Evm.W)
    (selected : live cell.val) (a : WordSpan μ.capacity)
    (aligned : a.offset.val.toNat=32*cell.val) :
    WordFrame (Evm.Memory.writeMachine m cell.val (.val w))
      (frameBytes (store32 μ a (Evm.Memory.indexValue w))) (fun c => live c ∨ c=cell.val) := by
  rw [frameBytes_store32,aligned]
  simp only [Evm.Memory.indexValue,Int.toNat_natCast]
  exact h.write cell.val w (h.fits cell.val selected)

/-- info: 'Solidity.Backend.MemoryOps.Physical.frame_wordByte' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms frame_wordByte
/-- info: 'Solidity.Backend.MemoryOps.Physical.frameBytes_store32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frameBytes_store32
/-- info: 'Solidity.Backend.MemoryOps.Physical.frame_store32_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frame_store32_target
/-- info: 'Solidity.Backend.MemoryOps.Physical.frame_snapshot_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frame_snapshot_read
/-- info: 'Solidity.Backend.MemoryOps.Physical.frameBytes_expandZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frameBytes_expandZero
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.frame_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.frame_store
end Solidity.Backend.MemoryOps.Physical
