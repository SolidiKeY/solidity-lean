import Solidity.Yul.World.PhysicalCompletion

namespace Solidity.Yul.World.PhysicalCompletion
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views

/-- Actual different-context slot bodies with a committed child remain
undoable at the outer three-journal mark. Trace conclusions are full lists. -/
theorem nested_commit_revert {E Γ ps ts q before} (F G : Fr)
    (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects E.layout E.lay E.lay) (same : o.effects.execution=s.2.ex)
    (owner : q.address=F.this) (next : PackedSlotRequest)
    (p2 : RepresentedSlotPlan ps ts next (requestEncoding ps ts q before)) (owner2 : next.address=G.this)
    (nonstatic : F.static=false) (childNonstatic : G.static=false)
    (prior suffix : List Observation) (childData outerData : Bytes) :
    let first := PhysicalSlotPort.step ps ts q before F p s r o same owner
    let firstObserved : ObservedEffects E.layout E.lay E.lay :=
      ⟨⟨first.2.effects.execution,committedLogs (o.trace++prior),[]⟩,o.trace++prior,rfl⟩
    let second := PhysicalSlotPort.step ps ts next (requestEncoding ps ts q before) G p2
      first.1.1.1.2 first.1.1.2 firstObserved rfl owner2
    let child := finish first.1.1.1.2 (requestEncoding ps ts q before) firstObserved
      (companionEnter ⟨first.2.effects.execution,first.1.1.2⟩ G.this G.sender G.value [] G.static)
      ⟨⟨second.1.1.1.2,second.1.1.2⟩,second.1.2⟩ suffix (.success childData)
    finish s before o (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value [] F.static)
      child.1 (prior++suffix) (.revert outerData) =
      (⟨⟨s,r⟩,before⟩,
        ⟨⟨s.2.ex,committedLogs (rollbackTrace o.trace (prior++suffix)),outerData⟩,
          rollbackTrace o.trace (prior++suffix),rfl⟩) ∧
    child.2.trace=(o.trace++prior)++suffix := by
  dsimp only
  rw [finish_success]
  unfold PhysicalSlotPort.step
  rw [representedSourceStep_nonstatic F p s r nonstatic]
  dsimp only
  rw [representedSourceStep_nonstatic G p2 _ _ childNonstatic]
  constructor
  · have restore := finish_runs_revert s r before o [p.packed.sourceOp,p2.packed.sourceOp]
      [p.packed.residualUpdate,p2.packed.residualUpdate]
      ((encodingWrites (selectedSlotPaths (if q.transient then ts q.address else ps q.address) q.slot)
          q.transient q.address (fun _=>q.raw) before) ++
       (encodingWrites (selectedSlotPaths (if next.transient then ts next.address else ps next.address) next.slot)
          next.transient next.address (fun _=>next.raw) (requestEncoding ps ts q before)))
      F.this F.sender F.value [] F.static (prior++suffix) outerData
    simpa only [ExecState.run,residualRun,boolEncodingRun_append,requestEncoding] using restore
  · rfl

end Solidity.Yul.World.PhysicalCompletion
