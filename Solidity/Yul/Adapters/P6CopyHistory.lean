import Solidity.Yul.Adapters.P6SnapshotCopy

/-! Chronological actual P6 copies with refreshed Source snapshot evidence.
At unsupported preparation, the first pending request HAS already copied its
bytes; later requests have not run. Its reached frame is retained and must not
be blindly replayed as an ordinary resumption. No new instruction AST, logical
state, gas policy or Source/Yul refusal is introduced. -/
namespace Solidity.Yul.Adapters.P6CopyHistory
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

/-- Existing bounded spans and their actual equal-length proof only. -/
abbrev SpanPair (capacity : Nat) :=
  Σ source : ByteSpan capacity, { destination : ByteSpan capacity // source.length=destination.length }

variable {C : Contract} {Δ : Ctx}

/-- Capacity transport does not change offsets or lengths. -/
def copy (capacity : Nat) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (spans : SpanPair capacity) : FrameMem C Δ :=
  P6ByteMemory.copySnapshot μ (bound.symm ▸ spans.1) (bound.symm ▸ spans.2.val)
    (by cases bound;exact spans.2.property)

theorem copy_capacity (capacity : Nat) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (spans : SpanPair capacity) : (copy capacity μ bound spans).capacity=capacity := by
  cases bound
  unfold copy P6ByteMemory.copySnapshot
  rw [P6ByteMemory.touch_capacity,P6ByteMemory.write_capacity]

structure Progress {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (capacity : Nat) (C : Contract) (Δ : Ctx) where
  current : Σ s : Source.EMState E Γ,SnapshotCursor allocated s
  frame : FrameMem C Δ
  bound : frame.capacity=capacity
  pending : List (SpanPair capacity)

/-- Actual finite input determines recursion, with no added resource cap.
Physical copy precedes canonical synchronization; only success advances Source. -/
def run {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (capacity : Nat) :
    (s : Source.EMState E Γ) → SnapshotCursor allocated s →
    (μ : FrameMem C Δ) → μ.capacity=capacity → List (SpanPair capacity) →
    Progress (Γ:=Γ) allocated capacity C Δ
  | s,c,μ,bound,[] => ⟨⟨s,c⟩,μ,bound,[]⟩
  | s,c,μ,bound,spans::rest =>
    let reached := copy capacity μ bound spans
    match snapshotStep allocated s c (frameBytes reached) with
    | none => ⟨⟨s,c⟩,reached,copy_capacity capacity μ bound spans,spans::rest⟩
    | some next => run allocated capacity next.1 next.2 reached (copy_capacity capacity μ bound spans) rest

/-- Every original heap typing survives all synchronized copies, including
prefixes stopped at a noncanonical physically reached image. -/
theorem run_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (capacity : Nat) (s : Source.EMState E Γ)
    (c : SnapshotCursor allocated s) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (requests : List (SpanPair capacity)) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (run allocated capacity s c μ bound requests).current.1 := by
  induction requests generalizing s μ with
  | nil => exact ok
  | cons spans rest ih =>
    unfold run
    dsimp only
    cases prepared : snapshotStep allocated s c (frameBytes (copy capacity μ bound spans)) with
    | none =>
      exact ok
    | some next =>
      exact ih next.1 next.2 _ _ (snapshotStep_MemOK allocated s c _ next prepared H ok)

/-- Whole nonheap administration, inventory identity and coverage transport
follow the real Source updates at every successful step. -/
theorem run_preserves {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (capacity : Nat) (s : Source.EMState E Γ)
    (c : SnapshotCursor allocated s) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (requests : List (SpanPair capacity)) :
    let out := (run allocated capacity s c μ bound requests).current
    out.1=withSourceHeap s out.1.2.heap ∧
      out.2.entries.map MixedHeapEntry.id=c.entries.map MixedHeapEntry.id ∧
      (CoversMixedHeap c.entries → CoversMixedHeap out.2.entries) := by
  induction requests generalizing s μ with
  | nil => exact ⟨(withSourceHeap_unchanged s).symm,rfl,id⟩
  | cons spans rest ih =>
    unfold run
    dsimp only
    cases prepared : snapshotStep allocated s c (frameBytes (copy capacity μ bound spans)) with
    | none => exact ⟨(withSourceHeap_unchanged s).symm,rfl,id⟩
    | some next =>
      have one := snapshotStep_preserves allocated s c _ next prepared
      have tail := ih next.1 next.2 (copy capacity μ bound spans) (copy_capacity capacity μ bound spans)
      refine ⟨tail.1.trans ?_,tail.2.1.trans one.2.2.2.2.2.1,
        fun full => tail.2.2 (one.2.2.2.2.2.2 full)⟩
      exact (congrArg (fun st => withSourceHeap st
        (run allocated capacity next.1 next.2 _ _ rest).current.1.2.heap) one.1).trans rfl

/-- No requested synchronization disappears: pending is the exact suffix.
Its first physical copy may already have happened, as stated in `run`. -/
theorem run_suffix {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (capacity : Nat) (s : Source.EMState E Γ)
    (c : SnapshotCursor allocated s) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (requests : List (SpanPair capacity)) :
    ∃ done,requests=done++(run allocated capacity s c μ bound requests).pending := by
  induction requests generalizing s μ with
  | nil => exact ⟨[],rfl⟩
  | cons spans rest ih =>
    unfold run
    dsimp only
    cases prepared : snapshotStep allocated s c (frameBytes (copy capacity μ bound spans)) with
    | none =>
      exact ⟨[],rfl⟩
    | some next =>
      obtain ⟨done,same⟩ := ih next.1 next.2 _ (copy_capacity capacity μ bound spans)
      exact ⟨spans::done,congrArg (List.cons spans) same⟩

/-- Stopping retains the exact failed reached bytes and the successful Source
prefix. This is preparation None, not a Source halt or a copy refusal. -/
theorem run_stopped {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (capacity : Nat) (s : Source.EMState E Γ)
    (c : SnapshotCursor allocated s) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (requests : List (SpanPair capacity)) (spans : SpanPair capacity) (rest : List (SpanPair capacity))
    (pending : (run allocated capacity s c μ bound requests).pending=spans::rest) :
    let out := run allocated capacity s c μ bound requests
    snapshotStep allocated out.current.1 out.current.2 (frameBytes out.frame)=none := by
  induction requests generalizing s μ with
  | nil => cases pending
  | cons first requests ih =>
    unfold run at pending ⊢
    dsimp only at pending ⊢
    cases prepared : snapshotStep allocated s c (frameBytes (copy capacity μ bound first)) with
    | none =>
      simp only [prepared]
    | some next =>
      simp only [prepared] at pending ⊢
      exact ih next.1 next.2 _ _ pending

/-- Complete successful sequences reencode the whole reached image. The empty
sequence requires its initial view, not a caller-supplied final-view equation. -/
theorem run_reencode {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (capacity : Nat) (s : Source.EMState E Γ)
    (c : SnapshotCursor allocated s) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (requests : List (SpanPair capacity))
    (initial : encodeMixedHeap c.placement c.entries (frameBytes μ)=frameBytes μ)
    (complete : (run allocated capacity s c μ bound requests).pending=[]) :
    let out := run allocated capacity s c μ bound requests
    encodeMixedHeap out.current.2.placement out.current.2.entries (frameBytes out.frame)=frameBytes out.frame := by
  induction requests generalizing s μ with
  | nil => exact initial
  | cons spans requests ih =>
    unfold run at complete ⊢
    dsimp only at complete ⊢
    cases prepared : snapshotStep allocated s c (frameBytes (copy capacity μ bound spans)) with
    | none => simp only [prepared] at complete;cases complete
    | some next =>
      simp only [prepared] at complete ⊢
      exact ih next.1 next.2 _ _ (snapshotStep_reencode allocated s c _ next prepared) complete

end Solidity.Yul.Adapters.P6CopyHistory
