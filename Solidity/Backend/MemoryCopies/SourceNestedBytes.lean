import Solidity.Backend.MemoryCopies.SourceNestedBytesInterface

/-! Actual Source nested byte child copies, preserving static storage inputs. -/
namespace Solidity.Backend.MemoryCopies

theorem PersistentSourceCell.transport {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {frame : Source.Fr} {path : Source.SPath} {before after : Source.EMState E Γ}
    {value : Source.Val E.layout τ} (cell : PersistentSourceCell frame path before value)
    (extension : AllocationExtension before after) : PersistentSourceCell frame path after value := by
  refine ⟨cell.typed,cell.persistent,?_⟩
  rw [extension.frame]
  exact cell.stored

theorem SourceByteRange.transport {E : Source.Env} {Γ : Source.RCtx}
    {frame : Source.Fr} {path : Source.SPath} {before after : Source.EMState E Γ}
    {start : Nat} {bytes : List UInt8} (cells : SourceByteRange frame path before start bytes)
    (extension : AllocationExtension before after) : SourceByteRange frame path after start bytes :=
  fun index => (cells index).transport extension

theorem StoredSourceBytes.transport {E : Source.Env} {Γ : Source.RCtx}
    {frame : Source.Fr} {path : Source.SPath} {before after : Source.EMState E Γ}
    {bytes : List UInt8} (input : StoredSourceBytes frame path before bytes)
    (extension : AllocationExtension before after) : StoredSourceBytes frame path after bytes :=
  ⟨input.range,input.length.transport extension,input.payload.transport extension⟩

theorem sourceByteChildren_run {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (children : List (List UInt8)) (start slack : Nat) (before : Source.EMState E Γ)
    (inputs : SourceByteChildren frame path before start children) :
    SourceByteChildrenResult frame path before start slack children := by
  induction children generalizing start slack before with
  | nil =>
    refine ⟨Fin.elim0,before,?_,rfl,AllocationExtension.refl before,?_,?_⟩
    · have budget : byteChildrenHorizon [] + slack = slack + 1 := by
        simp only [byteChildrenHorizon]
        omega
      rw [budget]
      rfl
    · intro index; exact Fin.elim0 index
    · intro index; exact Fin.elim0 index
  | cons bytes rest previous =>
    have headInput : StoredSourceBytes frame (path.go (.index start)) before bytes := by
      simpa only [List.getElem_cons_zero,Nat.add_zero] using inputs ⟨0,by simp only [List.length_cons]; omega⟩
    let one : Source.EMState E Γ := allocatedState (Source.Data.bytes (l := .memory) bytes) before
    have first : SourceStorageCopyCertificate frame (bytes.length + 2 + (byteChildrenHorizon rest + slack))
        (.bytes .memory) rfl (path.go (.index start)) before before one before.2.heap.next (Source.Data.bytes bytes) :=
      sourceBytesCopy frame _ before bytes (byteChildrenHorizon rest + slack)
        headInput.range headInput.length headInput.payload
    have firstFrame : AllocationExtension before one := AllocatesOnly.alloc (Source.Data.bytes (l := .memory) bytes) before
    have restInputs : SourceByteChildren frame path one (start + 1) rest := by
      intro index
      have input : StoredSourceBytes frame (path.go (.index (start + (index.val + 1)))) before rest[index] :=
        inputs ⟨index.val + 1,by simp only [List.length_cons]; omega⟩
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using input.transport firstFrame
    obtain ⟨values,after,tailRun,frontier,preserved,identities,contents⟩ :=
      previous (start := start + 1) (slack := bytes.length + 3 + slack) (before := one) restInputs
    have firstRun :
        (Source.loadElem (E := E) (Γ := Γ) frame (bytes.length + 3 + byteChildrenHorizon rest + slack)
          (.bytes .memory) (path.go (.index start))).run before =
          (.ok (.memRef rfl before.2.heap.next),one) := by
      have budget : bytes.length + 2 + (byteChildrenHorizon rest + slack) + 1 =
          bytes.length + 3 + byteChildrenHorizon rest + slack := by omega
      simpa only [budget] using first.execution
    have restRun :
        (Source.loadElems (E := E) (Γ := Γ) frame (bytes.length + 3 + byteChildrenHorizon rest + slack)
          (.bytes .memory) path (start + 1) rest.length).run one = (.ok values,after) := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tailRun
    refine ⟨Source.finCons (.val (.memRef rfl before.2.heap.next)) values,after,?_,?_,
      firstFrame.trans preserved,?_,?_⟩
    · have budget : byteChildrenHorizon (bytes :: rest) + slack =
          (bytes.length + 3 + byteChildrenHorizon rest + slack) + 1 := by
        simp only [byteChildrenHorizon]
        omega
      rw [budget]
      change (do
        let value ← Source.loadElem (E := E) (Γ := Γ) frame
          (bytes.length + 3 + byteChildrenHorizon rest + slack) (.bytes .memory) (path.go (.index start))
        let tail ← Source.loadElems frame (bytes.length + 3 + byteChildrenHorizon rest + slack)
          (.bytes .memory) path (start + 1) rest.length
        pure (Source.finCons (Source.Data.val value) tail)).run before = _
      rw [Source.Hoare.run_bind,firstRun]
      dsimp only
      rw [Source.Hoare.run_bind,restRun]
      rfl
    · change after.2.heap.next = before.2.heap.next + (rest.length + 1)
      change after.2.heap.next = before.2.heap.next + 1 + rest.length at frontier
      omega
    · intro index
      rcases index with ⟨index,bound⟩
      simp only [List.length_cons] at bound
      cases index with
      | zero => rfl
      | succ index =>
        change values ⟨index,by omega⟩ = .val (.memRef rfl (before.2.heap.next + (index + 1)))
        rw [identities]
        congr 2
        change before.2.heap.next + 1 + index = before.2.heap.next + (index + 1)
        omega
    · intro index
      rcases index with ⟨index,bound⟩
      simp only [List.length_cons] at bound
      cases index with
      | zero =>
        change after.2.heap.get before.2.heap.next = some ⟨.bytes .memory,Source.Data.bytes bytes⟩
        rw [preserved.old before.2.heap.next (by change before.2.heap.next < before.2.heap.next + 1; omega)]
        exact first.object
      | succ index =>
        have stored : after.2.heap.get (one.2.heap.next + index) =
            some ⟨.bytes .memory,Source.Data.bytes rest[(⟨index,by omega⟩ : Fin rest.length)]⟩ := contents ⟨index,by omega⟩
        change after.2.heap.get (before.2.heap.next + 1 + index) =
          some ⟨.bytes .memory,Source.Data.bytes rest[(⟨index,by omega⟩ : Fin rest.length)]⟩ at stored
        change after.2.heap.get (before.2.heap.next + (index + 1)) = _
        have address : before.2.heap.next + (index + 1) = before.2.heap.next + 1 + index := by omega
        rw [address]
        exact stored

/-- Complete dynamic parent copying after all populated byte children. Both
the load and fresh parent allocation are derived from actual static inputs. -/
theorem sourceNestedBytes_copy {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (children : List (List UInt8)) (slack : Nat)
    (range : Source.IntTy.u256.lo ≤ (children.length : Int) ∧ (children.length : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int children.length range))
    (inputs : SourceByteChildren frame path before 0 children) :
    ∃ (values : Fin children.length → Source.Data E.layout (.bytes .memory)) (loaded : Source.EMState E Γ),
      let data : Source.Data E.layout (.array .memory (.bytes .memory) none) :=
        .array children.length (fun _ impossible => nomatch impossible) values
      SourceStorageCopyCertificate frame (byteChildrenHorizon children + 1 + slack)
        (.array .memory (.bytes .memory) none) rfl path before loaded (allocatedState data loaded) loaded.2.heap.next data ∧
      loaded.2.heap.next = before.2.heap.next + children.length ∧
      (∀ index : Fin children.length, values index = .val (.memRef rfl (before.2.heap.next + index.val))) ∧
      (∀ index : Fin children.length, (allocatedState data loaded).2.heap.get (before.2.heap.next + index.val) =
        some ⟨.bytes .memory,Source.Data.bytes children[index]⟩) := by
  obtain ⟨values,loaded,execution,frontier,_,identities,contents⟩ :=
    sourceByteChildren_run frame path children 0 slack before inputs
  let data : Source.Data E.layout (.array .memory (.bytes .memory) none) :=
    .array children.length (fun _ impossible => nomatch impossible) values
  have sizeRead : (Source.readLen (E := E) (Γ := Γ) frame path).run before = (.ok children.length,before) := by
    rw [Source.readLen,Source.Hoare.run_bind,length.read]
    rfl
  have load : (Source.loadMem (E := E) (Γ := Γ) frame (byteChildrenHorizon children + 1 + slack)
      (.array .memory (.bytes .memory) none) path).run before = (.ok data,loaded) := by
    have budget : byteChildrenHorizon children + 1 + slack = (byteChildrenHorizon children + slack) + 1 := by omega
    rw [budget,Source.loadMem,Source.Hoare.run_bind,sizeRead]
    dsimp only
    rw [Source.Hoare.run_bind,execution]
    rfl
  refine ⟨values,loaded,storageCopyCertificate frame _ _ rfl path before loaded data load,frontier,identities,?_⟩
  intro index
  have older : before.2.heap.next + index.val < loaded.2.heap.next := by
    rw [frontier]
    exact Nat.add_lt_add_left index.isLt _
  exact (Source.Heap.alloc_other loaded.2.heap ⟨.array .memory (.bytes .memory) none,data⟩
    (Nat.ne_of_lt older)).trans (contents index)

#print axioms PersistentSourceCell.transport
#print axioms SourceByteRange.transport
#print axioms StoredSourceBytes.transport
#print axioms sourceByteChildren_run
#print axioms sourceNestedBytes_copy
end Solidity.Backend.MemoryCopies
