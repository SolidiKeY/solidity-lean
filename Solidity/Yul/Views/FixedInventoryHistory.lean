import Solidity.Yul.Views.FixedInventoryCursor
import Solidity.Yul.Views.InventorySnapshotHistory

/-! Chronological supplied fixed/nominal snapshots reuse the existing progress
and cursor carriers. Each successful prefix executes actual typed Source writes;
unsupported preparation retains the exact remaining suffix. These laws do not
instrument recursive Source evaluation or establish snapshot provenance. -/
namespace Solidity.Yul.Views.FixedInventory
open NominalInventory (SnapshotCursor SnapshotProgress)

/-- Stop BEFORE executing an unsupported snapshot; keep all prior Source writes. -/
def runSnapshots {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) : (s : Source.EMState E Γ) → SnapshotCursor allocated s →
      List ByteView → SnapshotProgress (Γ:=Γ) allocated
  | s,c,[] => ⟨⟨s,c⟩,[]⟩
  | s,c,m::ms =>
    match snapshotStep allocated s c m with
    | none => ⟨⟨s,c⟩,m::ms⟩
    | some next => runSnapshots allocated next.1 next.2 ms

/-- A successful singleton returns the exact dependent step result. -/
theorem runSnapshots_single {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) (next : Σ t,SnapshotCursor allocated t)
    (step : snapshotStep allocated s c m=some next) :
    runSnapshots allocated s c [m]=⟨next,[]⟩ := by
  simp only [runSnapshots,step]

/-- Every original owner typing survives the successful prefix, even when
later canonical preparation is unsupported. -/
theorem runSnapshots_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (ms : List ByteView) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (runSnapshots allocated s c ms).current.1 := by
  first
  | solve | simp only
  | induction ms generalizing s with
    | nil => exact ok
    | cons m ms ih =>
      unfold runSnapshots
      cases step : snapshotStep allocated s c m with
      | none => exact ok
      | some next => exact ih next.1 next.2 (snapshotStep_MemOK allocated s c m next step H ok)

/-- Coverage, inventory identity, placement/free choice, heap typing/next and
WHOLE administrative state are retained through arbitrary snapshot changes. -/
theorem runSnapshots_preserves {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (ms : List ByteView) :
    let out := (runSnapshots allocated s c ms).current
    out.1=withSourceHeap s out.1.2.heap ∧ out.1.2.heap.ty=s.2.heap.ty ∧
    out.1.2.heap.next=s.2.heap.next ∧ out.2.placement.address=c.placement.address ∧
    out.2.placement.free=c.placement.free ∧
    out.2.entries.map MixedHeapEntry.id=c.entries.map MixedHeapEntry.id ∧
    (CoversMixedHeap c.entries → CoversMixedHeap out.2.entries) := by
  first
  | solve | simp only
  | induction ms generalizing s with
    | nil => exact ⟨(withSourceHeap_unchanged s).symm,rfl,rfl,rfl,rfl,rfl,id⟩
    | cons m ms ih =>
      unfold runSnapshots
      cases step : snapshotStep allocated s c m with
      | none => exact ⟨(withSourceHeap_unchanged s).symm,rfl,rfl,rfl,rfl,rfl,id⟩
      | some next =>
        have one := snapshotStep_preserves allocated s c m next step
        have tail := ih next.1 next.2
        refine ⟨tail.1.trans ?_,tail.2.1.trans one.2.1,tail.2.2.1.trans one.2.2.1,
          tail.2.2.2.1.trans one.2.2.2.1,tail.2.2.2.2.1.trans one.2.2.2.2.1,
          tail.2.2.2.2.2.1.trans one.2.2.2.2.2.1,fun full => tail.2.2.2.2.2.2 (one.2.2.2.2.2.2 full)⟩
        exact (congrArg (fun st => withSourceHeap st
          (runSnapshots allocated next.1 next.2 ms).current.1.2.heap) one.1).trans rfl

/-- Pending is the exact unexecuted suffix: its first snapshot cannot prepare
against the retained prefix state/cursor. It is not an execution error code. -/
theorem runSnapshots_stopped {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (ms : List ByteView) (m : ByteView) (rest : List ByteView)
    (pending : (runSnapshots allocated s c ms).pending=m::rest) :
    let out := (runSnapshots allocated s c ms).current
    snapshotStep allocated out.1 out.2 m=none := by
  first
  | solve | simp only at pending ⊢
  | induction ms generalizing s with
    | nil => cases pending
    | cons a ms ih =>
      unfold runSnapshots at pending ⊢
      cases step : snapshotStep allocated s c a with
      | none =>
        simp only [step] at pending ⊢
        cases pending
        exact step
      | some next =>
        simp only [step] at pending ⊢
        exact ih next.1 next.2 pending

/-- Concatenation preserves exact prefixes. An unsupported earlier snapshot
retains its original state and appends the untouched later inputs to pending. -/
theorem runSnapshots_append {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (xs ys : List ByteView) :
    runSnapshots allocated s c (xs++ys)=
      let done := runSnapshots allocated s c xs
      if done.pending.isEmpty then runSnapshots allocated done.current.1 done.current.2 ys
      else ⟨done.current,done.pending++ys⟩ := by
  first
  | solve | simp only
  | induction xs generalizing s with
    | nil => rfl
    | cons m xs ih =>
      simp only [List.cons_append,runSnapshots]
      cases step : snapshotStep allocated s c m with
      | none => rfl
      | some next => exact ih next.1 next.2

/-- No input snapshots disappear: pending is an actual suffix of the supplied
chronological list, including the first unsupported preparation if any. -/
theorem runSnapshots_suffix {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (ms : List ByteView) :
    ∃ done,ms=done++(runSnapshots allocated s c ms).pending := by
  first
  | solve | simp only
  | induction ms generalizing s with
    | nil => exact ⟨[],rfl⟩
    | cons m ms ih =>
      unfold runSnapshots
      cases step : snapshotStep allocated s c m with
      | none => exact ⟨[],rfl⟩
      | some next =>
        obtain ⟨done,same⟩ := ih next.1 next.2
        exact ⟨m::done,congrArg (List.cons m) same⟩

/-- Complete-prefix execution resumes from the actual returned state/cursor. -/
theorem runSnapshots_resume {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (xs ys : List ByteView) (complete : (runSnapshots allocated s c xs).pending=[]) :
    runSnapshots allocated s c (xs++ys)=
      runSnapshots allocated (runSnapshots allocated s c xs).current.1
        (runSnapshots allocated s c xs).current.2 ys := by
  simp only [runSnapshots_append,complete,List.isEmpty_nil,↓reduceIte]

/-- Completing a nonempty snapshot sequence reconstructs the entire LAST
supplied raw map, including its residual bytes, from the final physical cursor. -/
theorem runSnapshots_reencode_last {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (xs : List ByteView) (m : ByteView)
    (complete : (runSnapshots allocated s c (xs++[m])).pending=[]) :
    let out := (runSnapshots allocated s c (xs++[m])).current
    encodeMixedHeap out.2.placement out.2.entries m=m := by
  first
  | solve | simp only
  | rw [runSnapshots_append] at complete ⊢
    dsimp only
    cases pending : (runSnapshots allocated s c xs).pending with
    | nil =>
      simp only [pending,List.isEmpty_nil,↓reduceIte] at complete ⊢
      simp only [runSnapshots] at complete ⊢
      cases step : snapshotStep allocated (runSnapshots allocated s c xs).current.1
          (runSnapshots allocated s c xs).current.2 m with
      | none => simp only [step] at complete; cases complete
      | some next =>
        exact snapshotStep_reencode allocated _ _ m next step
    | cons a rest =>
      simp only [pending,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte,List.cons_append] at complete
      cases complete

end Solidity.Yul.Views.FixedInventory
