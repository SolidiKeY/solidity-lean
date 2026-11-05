import Solidity.Yul.Adapters.P6ResidualSequence

/-! Capacity preparation for the existing actual P6 copy runner. The successful
physical prefix is retained with the exact pending requests. An unready request
is unsupported component preparation, not a Source/Yul halt, native MCOPY error
or allocator verdict. No new runtime limit, source state or instruction AST. -/
namespace Solidity.Yul.Adapters.P6ResidualCapacity
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ResidualSequence
variable {C : Contract} {Δ : Ctx}

/-- Only the existing arithmetic room predicate is decided. -/
def roomDecision {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (capacity : Nat) (r : ResidualCopyRequest p) : Decidable (CopyRoom capacity r) := by
  unfold CopyRoom
  infer_instance

structure CopyProgress {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (C : Contract) (Δ : Ctx) where
  frame : FrameMem C Δ
  pending : List (ResidualCopyRequest p)

/-- Check actual capacity before each copy; never execute a failing request. -/
def checkedCopies {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) : List (ResidualCopyRequest p) → CopyProgress p C Δ
  | [] => ⟨μ,[]⟩
  | r::rest =>
    @dite (CopyProgress p C Δ) (CopyRoom μ.capacity r) (roomDecision μ.capacity r)
      (fun ready => checkedCopies (P6ResidualCopy.copyFrame μ r ready.1 ready.2) rest)
      (fun _ => ⟨μ,r::rest⟩)

/-- The old runner's premises are CONSTRUCTED for the executed prefix, not
supplied by callers or assumed as a finished execution/view law. -/
theorem checked_prefix {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (requests : List (ResidualCopyRequest p)) :
    ∃ done,requests=done++(checkedCopies μ requests).pending ∧
      ∃ rooms : ∀ r ∈ done,CopyRoom μ.capacity r,
        (checkedCopies μ requests).frame=runCopies μ done rooms := by
  first
  | solve | simp only [checkedCopies]
  | induction requests generalizing μ with
    | nil =>
      have emptyRooms : ∀ r ∈ ([] : List (ResidualCopyRequest p)),CopyRoom μ.capacity r := by
        intro r member;cases member
      exact ⟨[],rfl,⟨emptyRooms,rfl⟩⟩
    | cons r rest ih =>
      unfold checkedCopies
      split
      · rename_i ready
        let next := P6ResidualCopy.copyFrame μ r ready.1 ready.2
        obtain ⟨done,split,rooms,same⟩ := ih next
        have capacity : next.capacity=μ.capacity := (P6ResidualCopy.copy_carrier μ r ready.1 ready.2).2.2
        have all : ∀ t ∈ r::done,CopyRoom μ.capacity t := by
          intro t member
          rcases List.mem_cons.mp member with eq | later
          · subst t;exact ready
          · rw [←capacity]
            exact rooms t later
        refine ⟨r::done,congrArg (List.cons r) split,⟨all,?_⟩⟩
        exact same
      · have emptyRooms : ∀ r ∈ ([] : List (ResidualCopyRequest p)),CopyRoom μ.capacity r := by
          intro r member;cases member
        exact ⟨[],rfl,⟨emptyRooms,rfl⟩⟩

/-- The first pending request fails its actual reached-capacity preparation. -/
theorem checked_stopped {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (requests : List (ResidualCopyRequest p)) (r : ResidualCopyRequest p)
    (rest : List (ResidualCopyRequest p)) (pending : (checkedCopies μ requests).pending=r::rest) :
    ¬CopyRoom (checkedCopies μ requests).frame.capacity r := by
  first
  | solve | simp only [checkedCopies] at pending ⊢
  | induction requests generalizing μ with
    | nil => cases pending
    | cons first rest ih =>
      unfold checkedCopies at pending ⊢
      letI := roomDecision μ.capacity first
      by_cases ready : CopyRoom μ.capacity first
      · simp only [dif_pos ready] at pending ⊢
        exact ih (P6ResidualCopy.copyFrame μ first ready.1 ready.2) pending
      · simp only [dif_neg ready] at pending ⊢
        cases pending
        exact ready

/-- Fresh complete-image and Source/reserved closure at the exact checked
prefix. No caller-supplied capacity list, output equality or safety field. -/
theorem checked_source {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p))
    (prepared : prepareHeapInventory p=.ok (generatedHeapEntries p))
    (supported : ∀ a ty d,s.2.heap.get a=some ⟨ty,d⟩ → TypeSupported E ty)
    (μ : FrameMem C Δ) (residual : ByteView)
    (initial : frameBytes μ=residualCopyPhysical p residual) (reserved : ReservedOK residual p.free) :
    ∃ done,requests=done++(checkedCopies μ requests).pending ∧
      frameBytes (checkedCopies μ requests).frame=residualCopyPhysical p (residualCopies done residual) ∧
      writeback s allocated p history (generatedHeapEntries p)
        (frameBytes (checkedCopies μ requests).frame)=some (.ok (),s) ∧
      ReservedOK (frameBytes (checkedCopies μ requests).frame) p.free ∧
      (checkedCopies μ requests).frame.st=μ.st ∧ (checkedCopies μ requests).frame.key=μ.key ∧
      (checkedCopies μ requests).frame.capacity=μ.capacity := by
  obtain ⟨done,split,rooms,same⟩ := checked_prefix μ requests
  have source := runCopies_source s allocated p history done prepared supported μ rooms residual initial reserved
  have carrier := runCopies_carrier μ done rooms
  refine ⟨done,split,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [same]
  · exact runCopies_image μ done rooms residual initial
  · exact source.1
  · exact source.2
  · exact carrier.1
  · exact carrier.2.1
  · exact carrier.2.2

end Solidity.Yul.Adapters.P6ResidualCapacity
