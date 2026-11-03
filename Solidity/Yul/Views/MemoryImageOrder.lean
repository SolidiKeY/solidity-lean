import Solidity.Yul.Views.ComputedAllocationWrite
import Solidity.Yul.Views.RetainedAllocationOrder

/-! Pointwise locality and disjoint update order for every existing intrinsic
memory-image constructor. Typed logical allocation commutes with writes to a
real old cell, independently of the allocated object's constructor. Raw-map
laws require real separated spans; they say nothing about aliased writes. -/
namespace Solidity.Yul.Views

theorem wordList_point_congr (ws : List Roadmap.Word) (m n : ByteView) (base i : Nat)
    (same : m i=n i) : wordListView ws m base i=wordListView ws n base i := by
  induction ws generalizing base with
  | nil => exact same
  | cons w ws ih =>
    unfold wordListView mstore
    split
    · rfl
    · exact ih (base+32)

/-- Encoding at a byte depends on at most that input byte, not other residual
locations. This includes pointer-valued aggregate word images. -/
theorem MemoryImage.point_congr {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (m n : ByteView) (base i : Nat) (same : m i=n i) : image.encode m base i=image.encode n base i := by
  cases image with
  | bytes bs bound | string bs bound =>
    dsimp only [MemoryImage.encode,bytesObjectView,copyBytes,mstore]
    split
    · rfl
    · split
      · rfl
      · exact same
  | words d ws encoded => exact wordList_point_congr ws m n base i same

/-- Whole-map commutation, across different heaps/types and all concrete image
families, follows from actual image spans and pointwise locality. -/
theorem MemoryImage.disjoint_commute {D D' : Source.Layout} {h : Source.Heap D} {h' : Source.Heap D'}
    {p : Placement h} {q : Placement h'} {τ σ : Source.STy} {d : Source.Data D τ} {e : Source.Data D' σ}
    (x : MemoryImage p d) (y : MemoryImage q e) (m : ByteView) (a b : Nat)
    (separate : a+x.span≤b ∨ b+y.span≤a) :
    y.encode (x.encode m a) b=x.encode (y.encode m b) a := by
  funext i
  by_cases outside : i<a ∨ a+x.span≤i
  · rw [x.residual (y.encode m b) a i outside]
    exact y.point_congr _ _ b i (x.residual m a i outside)
  · have other : i<b ∨ b+y.span≤i := by omega
    rw [y.residual (x.encode m a) b i other]
    exact (x.point_congr _ _ a i (y.residual m b i other)).symm

/-- Generic object encoding commutes with a genuinely disjoint raw word write. -/
theorem MemoryImage.mstore_commute {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (m : ByteView) (base wordBase : Nat) (w : Roadmap.Word)
    (separate : base+image.span≤wordBase ∨ wordBase+32≤base) :
    image.encode (mstore m wordBase w) base=mstore (image.encode m base) wordBase w := by
  funext i
  by_cases atWord : wordBase≤i ∧ i<wordBase+32
  · have outside : i<base ∨ base+image.span≤i := by omega
    rw [image.residual _ _ _ outside]
    simp only [mstore,dif_pos atWord]
  · rw [mstore_outside _ _ _ _ (by omega)]
    exact image.point_congr _ _ base i (mstore_outside _ _ _ _ (by omega))

/-- The actual generic allocation encoder (new object PLUS FMP) commutes
with an old disjoint word update, including its precise preparation None. -/
theorem objectAllocationView_mstore_commute {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    {τ : Source.STy} (data : Source.Data D τ) (memory : τ.loc?=some .memory)
    (shape : MemoryShape) (shaped : HasMemoryShape data shape) (base : Nat) (free : Roadmap.Word)
    (after : p.free.val≤base) (fresh : ∀ a,(h.cells a).isSome → p.address a≠base)
    (fits : base+shape.size≤free.val) (m : ByteView) (wordBase : Nat) (w : Roadmap.Word)
    (start : 128≤wordBase) (before : wordBase+32≤base) :
    objectAllocationView h p data memory shape shaped base free after fresh fits (mstore m wordBase w)=
      (objectAllocationView h p data memory shape shaped base free after fresh fits m).map
        (fun raw=>mstore raw wordBase w) := by
  unfold objectAllocationView
  dsimp only
  cases ready : prepareHeapImage (heapAllocPlacement h p data shape shaped base free after fresh fits)
      h.next τ data (Source.Heap.alloc_get h _) with
  | none => rfl
  | some image =>
    change some (image.encode (mstore (mstore m wordBase w) 64 free) base)=
      some (mstore (image.encode (mstore m 64 free) base) wordBase w)
    rw [mstore_disjoint_commute m wordBase 64 w free (Or.inr (by omega))]
    exact congrArg some (image.mstore_commute _ base wordBase w (Or.inr before))

/-- Actual Source programs, complete state and returned reference, for EVERY
memory object. The existing typed old target is essential to commutation. -/
theorem heapPut_objectAllocRef_commute {E Γ} (s : Source.EMState E Γ) (a : Nat) {τ σ : Source.STy}
    (d : Source.Data E.layout τ) (typed : s.2.heap.ty a=some τ)
    (new : Source.Data E.layout σ) (memory : σ.loc?=some .memory) :
    ((do Source.heapPut a ⟨τ,d⟩; Source.allocRef new) : Source.EM E Γ (Source.Val E.layout σ)).run s=
    ((do let v ← Source.allocRef new; Source.heapPut a ⟨τ,d⟩; pure v) : Source.EM E Γ (Source.Val E.layout σ)).run s := by
  rw [Source.Hoare.run_bind,heapPutConcrete_run s a d typed]
  simp only []
  rw [objectAllocRef_run _ new memory,Source.Hoare.run_bind,objectAllocRef_run s new memory]
  simp only []
  rw [Source.Hoare.run_bind,heapPutConcrete_run _ a d (heap_alloc_old_type s.2.heap ⟨σ,new⟩ a τ typed)]
  change (Except.ok (Source.Val.memRef memory s.2.heap.next),
    withSourceHeap s ((s.2.heap.write a d typed).alloc ⟨σ,new⟩).1)=
    (Except.ok (Source.Val.memRef memory s.2.heap.next),withSourceHeap s ((s.2.heap.alloc ⟨σ,new⟩).1.write a d _))
  rw [heap_write_alloc]
end Solidity.Yul.Views
