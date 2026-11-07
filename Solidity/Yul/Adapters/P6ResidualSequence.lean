import Solidity.Yul.Adapters.P6ResidualCopy

/-! Finite sequences of actual bounded P6 copies. Requests and byte semantics
are reused; each source sees the reached frame of the preceding copy. Capacity
premises transport through proved capacity identity. Source writeback is proved
at sequence boundaries/prefixes, not inserted into the Source evaluator. -/
namespace Solidity.Yul.Adapters.P6ResidualSequence
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Δ : Ctx}

/-- Only the actual two capacity intervals, separate from request Word ranges. -/
def CopyRoom {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (capacity : Nat) (request : ResidualCopyRequest p) : Prop :=
  (request.window.size.val=0 ∨ request.source.val+request.window.size.val≤capacity) ∧
  (request.window.size.val=0 ∨ request.window.destination.val+request.window.size.val≤capacity)

/-- Structural recursion on actual requests; no separate node/fuel/length cap. -/
def runCopies {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) : (requests : List (ResidualCopyRequest p)) →
      (∀ r ∈ requests,CopyRoom μ.capacity r) → FrameMem C Δ
  | [],_ => μ
  | request::rest,rooms =>
    let next := P6ResidualCopy.copyFrame μ request (rooms request List.mem_cons_self).1
      (rooms request List.mem_cons_self).2
    runCopies next rest (fun r member => by
      have capacity := (P6ResidualCopy.copy_carrier μ request
        (rooms request List.mem_cons_self).1 (rooms request List.mem_cons_self).2).2.2
      change CopyRoom next.capacity r
      rw [capacity]
      exact rooms r (List.mem_cons_of_mem _ member))

/-- Fresh complete-image transport for ALL actual copies, including overlaps. -/
theorem runCopies_image {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (requests : List (ResidualCopyRequest p))
    (rooms : ∀ r ∈ requests,CopyRoom μ.capacity r) (residual : ByteView)
    (initial : frameBytes μ=residualCopyPhysical p residual) :
    frameBytes (runCopies μ requests rooms)=residualCopyPhysical p (residualCopies requests residual) := by
  first
  | solve | simp only [runCopies,residualCopies]
  | induction requests generalizing μ residual with
    | nil => exact initial
    | cons request rest ih =>
      unfold runCopies residualCopies
      apply ih
      exact P6ResidualCopy.copy_image μ request _ _ residual initial

/-- Whole carried state/key and capacity are preserved; high-water need not be. -/
theorem runCopies_carrier {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (requests : List (ResidualCopyRequest p))
    (rooms : ∀ r ∈ requests,CopyRoom μ.capacity r) :
    (runCopies μ requests rooms).st=μ.st ∧ (runCopies μ requests rooms).key=μ.key ∧
      (runCopies μ requests rooms).capacity=μ.capacity := by
  first
  | solve | simp only [runCopies]
  | induction requests generalizing μ with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | cons request rest ih =>
      unfold runCopies
      have one := P6ResidualCopy.copy_carrier μ request (rooms request List.mem_cons_self).1 (rooms request List.mem_cons_self).2
      have tail := ih (P6ResidualCopy.copyFrame μ request (rooms request List.mem_cons_self).1 (rooms request List.mem_cons_self).2) (fun r member => by
        rw [one.2.2]
        exact rooms r (List.mem_cons_of_mem _ member))
      exact ⟨tail.1.trans one.1,tail.2.1.trans one.2.1,tail.2.2.trans one.2.2⟩

/-- Actual whole-Source writeback identity at the reached frame; reserved words
and the full raw complement are retained for the existing canonical profile. -/
theorem runCopies_source {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p))
    (prepared : prepareHeapInventory p=.ok (generatedHeapEntries p))
    (supported : ∀ a ty d,s.2.heap.get a=some ⟨ty,d⟩ → TypeSupported E ty)
    (μ : FrameMem C Δ) (rooms : ∀ r ∈ requests,CopyRoom μ.capacity r)
    (residual : ByteView) (initial : frameBytes μ=residualCopyPhysical p residual)
    (reserved : ReservedOK residual p.free) :
    writeback s allocated p history (generatedHeapEntries p) (frameBytes (runCopies μ requests rooms))=
      some (.ok (),s) ∧ ReservedOK (frameBytes (runCopies μ requests rooms)) p.free := by
  rw [runCopies_image μ requests rooms residual initial]
  have inventory := prepareHeapInventory_ok p _ prepared
  exact ⟨writeback_encoded s allocated p history _ inventory.2.1 inventory.2.2
      (fun e _ => supported e.id e.ty e.data e.found) _,
    encodeMixedHeap_reserved p _ _ (residualCopies_reserved requests residual reserved)⟩

/-- A prefix length selects actual input, not a new bound. Every prefix has
its own reached frame, full view and actual whole-Source identity. -/
theorem runCopies_prefix {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p))
    (prepared : prepareHeapInventory p=.ok (generatedHeapEntries p))
    (supported : ∀ a ty d,s.2.heap.get a=some ⟨ty,d⟩ → TypeSupported E ty)
    (μ : FrameMem C Δ) (rooms : ∀ r ∈ requests,CopyRoom μ.capacity r)
    (residual : ByteView) (initial : frameBytes μ=residualCopyPhysical p residual)
    (reserved : ReservedOK residual p.free) (count : Nat) :
    let selected := requests.take count
    let result := runCopies μ selected (fun r member => rooms r (List.mem_of_mem_take member))
    frameBytes result=residualCopyPhysical p (residualCopies selected residual) ∧
    writeback s allocated p history (generatedHeapEntries p) (frameBytes result)=some (.ok (),s) ∧
    ReservedOK (frameBytes result) p.free := by
  first
  | solve | simp only
  | exact ⟨runCopies_image μ _ _ residual initial,
      runCopies_source s allocated p history _ prepared supported μ _ residual initial reserved⟩

/-- The reached image fits its actual reached accounting, not the old extent. -/
theorem runCopies_fits {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (μ : FrameMem C Δ) (requests : List (ResidualCopyRequest p))
    (rooms : ∀ r ∈ requests,CopyRoom μ.capacity r) :
    MemoryAgreement.Fits (runCopies μ requests rooms) (frameBytes (runCopies μ requests rooms)) :=
  MemoryAgreement.fits_view _

end Solidity.Yul.Adapters.P6ResidualSequence
