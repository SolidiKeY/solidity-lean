import Solidity.Yul.Views.ByteElementStore

/-! Physical byte transport through actual local substitution and explicit
source rollback. Caller locals survive both sub outcomes. A late halt or
rollbackTo does not invent heap restoration; the byte mutation remains live. -/
namespace Solidity.Yul.Views.ByteElementFrames

theorem sub_success {E Γ Δ} (s : Source.EMState E Γ) (child : Source.Locals E.layout Δ)
    (F : Source.Fr) (horizon root : Nat) (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) :
    (Source.EM.sub child (Source.writeLoc F horizon (.memByte root index.val)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl))).run s=
    (.ok ((),child),withSourceHeap s (s.2.heap.write root (heapByteData E.layout string (bytes.set index.val value))
      (heap_ty_of_get _ _ _ _ found))) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have run := ByteElementStore.source_run (⟨child,s.2⟩ : Source.EMState E Δ)
    F horizon root string bytes found index value
  simp only [ExceptT.run] at run
  unfold Source.EM.sub
  simp only [ExceptT.run,ExceptT.mk,run]
  rfl

theorem sub_halt {E Γ Δ} (s : Source.EMState E Γ) (child : Source.Locals E.layout Δ)
    (F : Source.Fr) (horizon root : Nat) (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) (reason : Source.Halt) :
    (Source.EM.sub child (do
      Source.writeLoc F horizon (.memByte root index.val)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl)
      (Source.EM.halt reason : Source.EM E Δ Unit))).run s=
    (.error reason,withSourceHeap s (s.2.heap.write root (heapByteData E.layout string (bytes.set index.val value))
      (heap_ty_of_get _ _ _ _ found))) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have run : ((do
      Source.writeLoc F horizon (.memByte root index.val)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl)
      (Source.EM.halt reason : Source.EM E Δ Unit))).run (child,s.2)=
      (.error reason,withSourceHeap (⟨child,s.2⟩ : Source.EMState E Δ)
        (s.2.heap.write root (heapByteData E.layout string (bytes.set index.val value))
          (heap_ty_of_get _ _ _ _ found))) := by
    rw [Source.Hoare.run_bind,ByteElementStore.source_run (⟨child,s.2⟩ : Source.EMState E Δ)
      F horizon root string bytes found index value]
    rfl
  simp only [ExceptT.run] at run
  unfold Source.EM.sub
  simp only [ExceptT.run,ExceptT.mk,run]
  rfl

theorem explicit_rollback {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root : Nat)
    (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) :
    ((do let checkpoint ← Source.mark
         Source.writeLoc F horizon (.memByte root index.val)
           (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl)
         Source.rollbackTo checkpoint) : Source.EM E Γ Unit).run s=
    (.ok (),withSourceHeap s (s.2.heap.write root (heapByteData E.layout string (bytes.set index.val value))
      (heap_ty_of_get _ _ _ _ found))) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold Source.mark
  rw [Source.Hoare.run_bind]
  change ((Source.writeLoc F horizon (.memByte root index.val)
    (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl) >>=
    fun _ => Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run s)=_
  rw [Source.Hoare.run_bind,ByteElementStore.source_run s F horizon root string bytes found index value]
  simp only [Source.rollbackTo,Source.EM.modSt]
  change ((Except.ok () : Source.R Unit), (s.1,{s.2 with
    heap:=s.2.heap.write root (heapByteData E.layout string (bytes.set index.val value)) (heap_ty_of_get _ _ _ _ found),
    ex:=s.2.ex.undoN (s.2.ex.journal.length-s.2.ex.journal.length),
    logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
  simp only [Nat.sub_self,Source.ExecState.undoN,List.drop_zero]
  rfl

/-- The same reached Source heap and physical patch work for a successful
substitution, a late child halt, and explicit rollbackTo. -/
theorem whole {E Γ Δ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (child : Source.Locals E.layout Δ) (reason : Source.Halt)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) (memory : ByteView)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let after := withSourceHeap s (s.2.heap.write root (heapByteData E.layout string (bytes.set index.val value))
      (heap_ty_of_get _ _ _ _ found))
    let q := ByteElementStore.placement s.2.heap p root string bytes found index value
    let patch := saveByte memory (p.address root+32+index.val) value
    (Source.EM.sub child (Source.writeLoc F horizon (.memByte root index.val)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl))).run s=(.ok ((),child),after) ∧
    (Source.EM.sub child (do
      Source.writeLoc F horizon (.memByte root index.val)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl)
      (Source.EM.halt reason : Source.EM E Δ Unit))).run s=(.error reason,after) ∧
    Source.MemOK E H after ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
    ∃ history : RetainedAllocation allocated q,
      enumeratedMemoryWriteback after allocated q history patch=.ok (some (.ok (),after)) ∧
      ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have physical := ByteElementStore.whole H s allocated p prior ok supported F horizon root string bytes found index value
    memory oldReads reserved
  exact ⟨sub_success s child F horizon root string bytes found index value,
    sub_halt s child F horizon root string bytes found index value reason,physical.2.1,physical.2.2.1,physical.2.2.2⟩
end Solidity.Yul.Views.ByteElementFrames
