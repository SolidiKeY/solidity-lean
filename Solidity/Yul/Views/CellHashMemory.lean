import Solidity.Yul.Views.CellWritesCalldataHash
import Solidity.Yul.Views.ComputedAllocationWrite

/-! Incremental physical realization of the actual calldata-hash allocation.
The existing computed encoder supplies header, payload and FMP, full raw-map
reconstruction and unchanged whole Source writeback. Computed placement is a
witness, not the target allocator policy; old image agreement remains explicit. -/
namespace Solidity.Yul.Views.CellHashMemory

def data {E : Source.Env} (F : Source.Fr) (off len : Nat) : Source.Data E.layout (.bytes .memory) :=
  .bytes ((F.cd.drop off).take len)

def shape (F : Source.Fr) (off len : Nat) : MemoryShape := .bytes ((F.cd.drop off).take len).length

def image {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (F : Source.Fr) (off len : Nat) (bound : p.free.val+max 1 (shape F off len).size<2^256)
    (memory : ByteView) : ByteView :=
  byteAllocationView ((F.cd.drop off).take len) p.free.val
    (ComputedAllocationWrite.nextFree p (shape F off len) bound)
    (by dsimp [ComputedAllocationWrite.nextFree,shape];omega) memory

theorem prepare_image {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (requests : List (FiniteCellWrites.Request E F.this)) (off len : Nat)
    (p : Placement (CellWritesCalldataHash.afterWrites F s requests).2.heap)
    (done : ComputedPlacement.prepare (CellWritesCalldataHash.afterWrites F s requests).2.heap=.ok p)
    (bound : p.free.val+max 1 (shape F off len).size<2^256) (memory : ByteView) :
    ComputedAllocationWrite.prepare _ p done (data (E:=E) F off len) (shape F off len) rfl bound memory=
      some (image p F off len bound memory) := by
  rfl

theorem image_payload {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (F : Source.Fr) (off len : Nat) (bound : p.free.val+max 1 (shape F off len).size<2^256)
    (memory : ByteView) :
    readBytes (image p F off len bound memory) (p.free.val+32) ((F.cd.drop off).take len).length=
      (F.cd.drop off).take len := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact byteAllocation_payload _ _ _ _ memory

theorem image_hash {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (G : Source.Glob E) (F : Source.Fr) (off len : Nat)
    (bound : p.free.val+max 1 (shape F off len).size<2^256) (memory : ByteView) :
    keccak256 G.fixed.evm (image p F off len bound memory) (p.free.val+32)
      ((F.cd.drop off).take len).length=G.fixed.hash ((F.cd.drop off).take len) := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact fixedHash_physical G.fixed _ _ _ _ (image_payload p F off len bound memory)

theorem image_residual {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (F : Source.Fr) (off len : Nat) (bound : p.free.val+max 1 (shape F off len).size<2^256)
    (memory : ByteView) (i : Nat)
    (outside : i<p.free.val ∨ p.free.val+32+((F.cd.drop off).take len).length≤i)
    (notFree : i<64 ∨ 96≤i) : image p F off len bound memory i=memory i := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact byteAllocation_residual _ _ _ _ memory i outside notFree

theorem observed {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (p : Placement (CellWritesCalldataHash.afterWrites F s requests).2.heap)
    (bound : p.free.val+max 1 (shape F off len).size<2^256) (memory : ByteView) :
    (((CellWritesCalldataHash.program G F (n+4) index requests >>= Source.getV).run s).1.map Source.Val.word)=
      .ok (some (keccak256 G.fixed.evm (image p F off len bound memory) (p.free.val+32)
        ((F.cd.drop off).take len).length)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [Source.Hoare.run_bind,CellWritesCalldataHash.run G F n s index off len requests allowed localValue]
  dsimp only
  exact congrArg Except.ok ((hashWord_observe E.layout (G.fixed.hash ((F.cd.drop off).take len))).trans
    (congrArg some (image_hash p G F off len bound memory).symm))

theorem realize {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (p : Placement (CellWritesCalldataHash.afterWrites F s requests).2.heap)
    (done : ComputedPlacement.prepare (CellWritesCalldataHash.afterWrites F s requests).2.heap=.ok p)
    (bound : p.free.val+max 1 (shape F off len).size<2^256)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) (memory : ByteView)
    (oldSupported : ∀ a τ d,(CellWritesCalldataHash.afterWrites F s requests).2.heap.get a=some ⟨τ,d⟩ →
      InventoryTypeSupported E τ)
    (reads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let current := CellWritesCalldataHash.afterWrites F s requests
    let object := data (E:=E) F off len
    let q := ComputedAllocationWrite.placement current.2.heap p done object (shape F off len) rfl bound
    let after := objectAllocatedState current object
    ∃ raw, ComputedAllocationWrite.prepare current.2.heap p done object (shape F off len) rfl bound memory=some raw ∧
      (CellWritesCalldataHash.program G F (n+4) index requests).run s=
        (.ok (.val (Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide)
          (Source.wordBytes (G.fixed.hash ((F.cd.drop off).take len))))),after) ∧
      Source.MemOK E H after ∧ CoversMixedHeap (generatedHeapEntries q) ∧
      encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      enumeratedMemoryWriteback after q q (retainInitial _ _) raw=.ok (some (.ok (),after)) ∧
      ReservedOK raw (ComputedAllocationWrite.nextFree p (shape F off len) bound) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let current := CellWritesCalldataHash.afterWrites F s requests
  have safe : Source.MemOK E H current := FiniteCellWrites.MemOK F s requests H ok
  obtain ⟨raw,step⟩ := Option.isSome_iff_exists.mp
    (ComputedAllocationWrite.complete current.2.heap p done (data (E:=E) F off len)
      (shape F off len) rfl bound memory trivial trivial (.bytes _))
  have sound := ComputedAllocationWrite.sound H current p done (data (E:=E) F off len)
    (shape F off len) rfl bound memory raw step safe trivial (.bytes _) trivial oldSupported reads
  exact ⟨raw,step,CellWritesCalldataHash.run G F n s index off len requests allowed localValue,
    sound.2.1,sound.2.2.1,sound.2.2.2.1,sound.2.2.2.2,
    ComputedAllocationWrite.reserved current.2.heap p done (data (E:=E) F off len)
      (shape F off len) rfl bound memory raw step reserved⟩
end Solidity.Yul.Views.CellHashMemory
