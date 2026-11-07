import Solidity.Yul.Adapters.P6ResidualResume

/-! Compute sufficient word-aligned representation capacity from the actual
pending copy intervals. Empty copies need no reservation at any offset. This
constructs bounded-frame preparation, not allocator or gas execution. -/
namespace Solidity.Yul.Adapters.P6ResidualReserve
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ResidualCapacity P6ResidualSequence P6ResidualResume
variable {C : Contract} {Δ : Ctx}
variable {D : Source.Layout} {h : Source.Heap D} {p : Placement h}

def requestExtent (r : ResidualCopyRequest p) : Nat :=
  if r.window.size.val=0 then 0 else
    max (r.source.val+r.window.size.val) (r.window.destination.val+r.window.size.val)

def extent : List (ResidualCopyRequest p) → Nat
  | [] => 0
  | r::rest => max (requestExtent r) (extent rest)

def extraWords (capacity required : Nat) : Nat := (required-capacity+31)/32

/-- Arithmetic derives room without an input list of safety witnesses. -/
theorem extent_room (requests : List (ResidualCopyRequest p)) (capacity : Nat)
    (fits : extent requests≤capacity) : ∀ r ∈ requests,CopyRoom capacity r := by
  first | (simp only [CopyRoom]; done) | skip
  induction requests with
  | nil => intro r member;cases member
  | cons first rest ih =>
    have bound : requestExtent first≤capacity ∧ extent rest≤capacity := by
      change max _ _≤capacity at fits
      omega
    intro r member
    rcases List.mem_cons.mp member with same | later
    · subst r
      unfold requestExtent at bound
      by_cases empty : first.window.size.val=0
      · exact ⟨Or.inl empty,Or.inl empty⟩
      · simp only [if_neg empty] at bound
        exact ⟨Or.inr (Nat.le_trans (Nat.le_max_left _ _) bound.1),
          Or.inr (Nat.le_trans (Nat.le_max_right _ _) bound.1)⟩
    · exact ih bound.2 r later

theorem reservation_fits (capacity required : Nat) :
    required≤capacity+extraWords capacity required*32 := by
  first | (simp only [extraWords]; omega) | rfl

/-- The computed extension is the least number of extra whole words. -/
theorem reservation_least (capacity required words : Nat)
    (fits : required≤capacity+words*32) : extraWords capacity required≤words := by
  first | (simp only [extraWords]; omega) | rfl

/-- Sufficient capacity makes the actual checked runner consume every request. -/
theorem checked_complete (μ : FrameMem C Δ) (requests : List (ResidualCopyRequest p))
    (rooms : ∀ r ∈ requests,CopyRoom μ.capacity r) :
    (checkedCopies μ requests).pending=[] := by
  first | (simp only [checkedCopies]; done) | skip
  induction requests generalizing μ with
  | nil => rfl
  | cons r rest ih =>
    have ready := rooms r List.mem_cons_self
    unfold checkedCopies
    rw [dif_pos ready]
    apply ih
    intro next member
    rw [(P6ResidualCopy.copy_carrier μ r ready.1 ready.2).2.2]
    exact rooms next (List.mem_cons_of_mem _ member)

/-- Reserve only for the actual pending suffix, then use the existing runner. -/
def finish (progress : CopyProgress p C Δ) : CopyProgress p C Δ :=
  resume progress (extraWords progress.frame.capacity (extent progress.pending))

theorem finish_complete (progress : CopyProgress p C Δ) : (finish progress).pending=[] := by
  apply checked_complete
  apply extent_room
  exact reservation_fits _ _

/-- A complete chronological output and actual whole Source identity follow
from computed reservation; capacity witnesses and a final output map are not
caller-supplied. Original canonical/placement/Word premises remain unchanged. -/
theorem finish_source {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p))
    (prepared : prepareHeapInventory p=.ok (generatedHeapEntries p))
    (supported : ∀ a ty d,s.2.heap.get a=some ⟨ty,d⟩ → TypeSupported E ty)
    (μ : FrameMem C Δ) (residual : ByteView)
    (initial : frameBytes μ=residualCopyPhysical p residual) (reserved : ReservedOK residual p.free) :
    frameBytes (finish (checkedCopies μ requests)).frame=
        residualCopyPhysical p (residualCopies requests residual) ∧
      writeback s allocated p history (generatedHeapEntries p)
        (frameBytes (finish (checkedCopies μ requests)).frame)=some (.ok (),s) ∧
      ReservedOK (frameBytes (finish (checkedCopies μ requests)).frame) p.free := by
  obtain ⟨before,after,split,image,source,valid,_⟩ :=
    resumed_source s allocated p history requests prepared supported μ residual initial reserved
      (extraWords (checkedCopies μ requests).frame.capacity (extent (checkedCopies μ requests).pending))
  have complete := finish_complete (checkedCopies μ requests)
  change requests=(before++after)++(finish (checkedCopies μ requests)).pending at split
  rw [complete,List.append_nil] at split
  exact ⟨split.symm ▸ image,source,valid⟩

end Solidity.Yul.Adapters.P6ResidualReserve
