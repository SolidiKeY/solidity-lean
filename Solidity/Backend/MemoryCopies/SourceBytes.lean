import Solidity.Backend.MemoryCopies.SourceBytesInterface

/-! Actual Source byte traversal from static cells, followed by fresh allocation. -/
namespace Solidity.Backend.MemoryCopies

theorem PersistentSourceCell.read {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    {value : Source.Val E.layout τ} (cell : PersistentSourceCell frame path before value) :
    (Source.readAt (E := E) (Γ := Γ) frame path τ).run before = (.ok value,before) :=
  Backend.Aggregates.SourceArray.read_typed E Γ frame before.2 before.1 path τ cell.typed value
    cell.persistent cell.stored

/-- Traverse the actual existing byte reader. The input fixes only primitive
storage cells; no desired loadBytes or loadMem result is assumed. -/
theorem sourceByteRange_run {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (bytes : List UInt8)
    (start slack : Nat) (cells : SourceByteRange frame path before start bytes) :
    (Source.loadBytes (E := E) (Γ := Γ) frame (bytes.length + 1 + slack) path start bytes.length).run before =
      (.ok bytes,before) := by
  induction bytes generalizing start with
  | nil =>
    have budget : ([] : List UInt8).length + 1 + slack = slack + 1 := by
      simp only [List.length_nil]
      omega
    rw [budget]
    rfl
  | cons byte rest previous =>
    have firstRun :
        (Source.readAt (E := E) (Γ := Γ) frame (path.go (.index start)) (.fixedBytes 1 (by decide))).run before =
          (.ok (.fixedBytes [byte] rfl),before) := by
      simpa only [List.getElem_cons_zero,Nat.add_zero] using
        (cells ⟨0,by simp only [List.length_cons]; omega⟩).read
    have restCells : SourceByteRange frame path before (start + 1) rest := by
      intro index
      have cell : PersistentSourceCell frame
          (path.go (.index (start + (index.val + 1)))) before
          (Source.Val.fixedBytes (n := 1) (h := by decide) [rest[index]] rfl) :=
        cells ⟨index.val + 1,by simp only [List.length_cons]; omega⟩
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cell
    have restRun :
        (Source.loadBytes (E := E) (Γ := Γ) frame (rest.length + 1 + slack) path (start + 1) rest.length).run before =
          (.ok rest,before) := previous (start + 1) restCells
    have budget : (byte :: rest).length + 1 + slack = (rest.length + 1 + slack) + 1 := by
      simp only [List.length_cons]
      omega
    rw [budget]
    change ((Source.readAt (E := E) (Γ := Γ) frame (path.go (.index start)) (.fixedBytes 1 (by decide))) >>= fun word =>
      match word with
      | .fixedBytes payload _ => do
        pure ((payload.headD 0) :: (← Source.loadBytes frame (rest.length + 1 + slack) path (start + 1) rest.length))).run before = _
    rw [Source.Hoare.run_bind,firstRun]
    change (do
      let payload ← Source.loadBytes (E := E) (Γ := Γ) frame (rest.length + 1 + slack) path (start + 1) rest.length
      pure (byte :: payload)).run before = _
    rw [Source.Hoare.run_bind,restRun]
    rfl

theorem sourceByteLength_run {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (bytes : List UInt8)
    (range : Source.IntTy.u256.lo ≤ (bytes.length : Int) ∧ (bytes.length : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int bytes.length range)) :
    (Source.readLen (E := E) (Γ := Γ) frame path).run before = (.ok bytes.length,before) := by
  rw [Source.readLen,Source.Hoare.run_bind,length.read]
  rfl

theorem sourceBytesLoad_run {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (bytes : List UInt8) (slack : Nat)
    (range : Source.IntTy.u256.lo ≤ (bytes.length : Int) ∧ (bytes.length : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int bytes.length range))
    (cells : SourceByteRange frame path before 0 bytes) :
    (Source.loadMem (E := E) (Γ := Γ) frame (bytes.length + 2 + slack) (.bytes .memory) path).run before =
      (.ok (.bytes bytes),before) := by
  have budget : bytes.length + 2 + slack = (bytes.length + 1 + slack) + 1 := by omega
  rw [budget,Source.loadMem,Source.Hoare.run_bind,sourceByteLength_run frame path before bytes range length]
  dsimp only
  rw [Source.Hoare.run_bind,sourceByteRange_run frame path before bytes 0 slack cells]
  rfl

/-- Inhabit the existing complete storage-copy certificate by a derived load,
then the existing actual root allocator. All old/nonheap fields are retained. -/
def sourceBytesCopy {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (bytes : List UInt8) (slack : Nat)
    (range : Source.IntTy.u256.lo ≤ (bytes.length : Int) ∧ (bytes.length : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int bytes.length range))
    (cells : SourceByteRange frame path before 0 bytes) :
    SourceStorageCopyCertificate frame (bytes.length + 2 + slack) (.bytes .memory) rfl path before before
      (allocatedState (Source.Data.bytes (l := .memory) bytes) before) before.2.heap.next (Source.Data.bytes bytes) :=
  storageCopyCertificate frame _ _ rfl path before before (.bytes bytes)
    (sourceBytesLoad_run frame path before bytes slack range length cells)

#print axioms PersistentSourceCell.read
#print axioms sourceByteRange_run
#print axioms sourceByteLength_run
#print axioms sourceBytesLoad_run
#print axioms sourceBytesCopy
end Solidity.Backend.MemoryCopies
