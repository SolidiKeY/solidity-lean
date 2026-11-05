import Solidity.Yul.Adapters.P6ResidualCapacity

/-! Resume bounded residual-copy preparation after the existing zero-capacity
extension. Executed requests are not replayed. This is representation capacity,
not a proof of allocation, gas accounting or native EVM memory expansion. -/
namespace Solidity.Yul.Adapters.P6ResidualResume
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ResidualCapacity
variable {C : Contract} {Δ : Ctx}

/-- Resume exactly the pending suffix, preserving the completed prefix. -/
def resume {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (progress : CopyProgress p C Δ) (extraWords : Nat) : CopyProgress p C Δ :=
  checkedCopies (expandZero progress.frame extraWords) progress.pending

/-- Reservation changes neither bytes nor resident accounting or carriers. -/
theorem extension_identity (μ : FrameMem C Δ) (extraWords : Nat) :
    frameBytes (expandZero μ extraWords)=frameBytes μ ∧
    (expandZero μ extraWords).st=μ.st ∧
    (expandZero μ extraWords).key=μ.key ∧
    (expandZero μ extraWords).highWaterWords=μ.highWaterWords ∧
    (expandZero μ extraWords).capacity=μ.capacity+extraWords*32 := by
  first
  | (simp only [expandZero]; done)
  | exact ⟨frameBytes_expandZero μ extraWords,rfl,rfl,rfl,rfl⟩

/-- Both successful prefixes are constructed by the actual checked runner.
The resulting complete physical map has the chronological residual updates and
unchanged whole Source state; insufficient extra capacity retains its suffix. -/
theorem resumed_source {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p))
    (prepared : prepareHeapInventory p=.ok (generatedHeapEntries p))
    (supported : ∀ a ty d,s.2.heap.get a=some ⟨ty,d⟩ → TypeSupported E ty)
    (μ : FrameMem C Δ) (residual : ByteView)
    (initial : frameBytes μ=residualCopyPhysical p residual) (reserved : ReservedOK residual p.free)
    (extraWords : Nat) :
    ∃ before after,
      requests=(before++after)++(resume (checkedCopies μ requests) extraWords).pending ∧
      frameBytes (resume (checkedCopies μ requests) extraWords).frame=
        residualCopyPhysical p (residualCopies (before++after) residual) ∧
      writeback s allocated p history (generatedHeapEntries p)
        (frameBytes (resume (checkedCopies μ requests) extraWords).frame)=some (.ok (),s) ∧
      ReservedOK (frameBytes (resume (checkedCopies μ requests) extraWords).frame) p.free ∧
      (resume (checkedCopies μ requests) extraWords).frame.st=μ.st ∧
      (resume (checkedCopies μ requests) extraWords).frame.key=μ.key ∧
      (resume (checkedCopies μ requests) extraWords).frame.capacity=μ.capacity+extraWords*32 := by
  obtain ⟨before,split,image,_,_,state,key,capacity⟩ :=
    checked_source s allocated p history requests prepared supported μ residual initial reserved
  have extended : frameBytes (expandZero (checkedCopies μ requests).frame extraWords)=
      residualCopyPhysical p (residualCopies before residual) :=
    (frameBytes_expandZero _ _).trans image
  obtain ⟨after,splitAfter,imageAfter,source,reservedAfter,stateAfter,keyAfter,capacityAfter⟩ :=
    checked_source s allocated p history (checkedCopies μ requests).pending prepared supported
      (expandZero (checkedCopies μ requests).frame extraWords) (residualCopies before residual)
      extended (residualCopies_reserved before residual reserved)
  refine ⟨before,after,?_,?_,source,reservedAfter,?_,?_,?_⟩
  · exact split.trans ((congrArg (List.append before) splitAfter).trans
      (List.append_assoc before after _).symm)
  · rw [residualCopies_append]
    exact imageAfter
  · exact stateAfter.trans state
  · exact keyAfter.trans key
  · exact capacityAfter.trans (congrArg (fun n => n+extraWords*32) capacity)

end Solidity.Yul.Adapters.P6ResidualResume
