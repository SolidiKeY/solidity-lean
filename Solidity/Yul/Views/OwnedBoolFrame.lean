import Solidity.Yul.Views.OwnedBoolSource

namespace Solidity.Yul.Views

/-- Public request binding uses the actual source frame's current account. -/
def representedFrameWrite? {E : Source.Env} {Γ : Source.RCtx}
    (ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a)))
    (F : Source.Fr) (bank : Bool) (slot raw : Roadmap.Word) (before : BoolEncodingJournal)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :=
  let q : PackedSlotRequest := ⟨bank,F.this,slot,raw⟩
  (prepareRepresentedSlot ps ts q before).map fun p => representedSourceStep ps ts q before F p s r

/-- Source frame rollback, complement rollback and owned-byte rollback refer to
the SAME checked action, not independently supplied source/residual runs. -/
theorem represented_step_rollback {E Γ ps ts q before}
    (F : Source.Fr) (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ) (r)
    (static : F.static=false) :
    let result := representedSourceStep ps ts q before F p s r
    companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.this 0 [] false)
      ⟨result.1.1.2.2.ex,result.1.2⟩=⟨s.2.ex,r⟩ ∧
    boolEncodingRollback before.journal.length result.2=before := by
  rw [representedSourceStep_nonstatic F p s r static]
  constructor
  · exact packed_frame_rollback ⟨s.2.ex,r⟩ [p.packed] F.this F.this 0 [] false
  · exact boolEncodingRollback_run before _

theorem represented_step_other_encoding {E Γ ps ts q before}
    (F : Source.Fr) (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ) (r)
    (static : F.static=false) (key : OwnedByteKey)
    (different : ∀ c ∈ selectedSlotPaths (if q.transient then ts q.address else ps q.address) q.slot,
      key≠ownedByteKey q.transient q.address c) :
    (representedSourceStep ps ts q before F p s r).2.cells key=before.cells key := by
  rw [representedSourceStep_nonstatic F p s r static]
  exact encodingWrites_other _ _ _ _ _ _ key different

theorem represented_step_persistent_at_request {E Γ ps ts q before}
    (F : Source.Fr) (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ) (r)
    (static : F.static=false) (bank : q.transient=false) (separated : finiteSeparated (ps q.address)) :
    let result := representedSourceStep ps ts q before F p s r
    reencodePersistentSlot (representedBanks ps false result.2)
      ⟨result.1.1.2.2.ex,result.1.2⟩ q.address q.slot=some q.raw := by
  have result := representedSourceStep_persistent F p s r static
    (by rw [p.request_eq]; exact bank) (by rw [p.request_eq]; exact separated)
  simpa only [p.request_eq] using result

/-- Two checked actual source actions may use different representation-indexed
registries. Committed child journals remain available to the enclosing mark. -/
theorem represented_two_outer_rollback {E Γ ps ts q before}
    (F : Source.Fr) (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ) (r)
    (next : PackedSlotRequest)
    (child : RepresentedSlotPlan ps ts next (requestEncoding ps ts q before))
    (static : F.static=false) :
    let first := representedSourceStep ps ts q before F p s r
    let second := representedSourceStep ps ts next (requestEncoding ps ts q before) F child first.1.1.2 first.1.2
    companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.this 0 [] false)
      (companionCommit (companionEnter ⟨first.1.1.2.2.ex,first.1.2⟩ F.this F.this 0 [] false)
        ⟨second.1.1.2.2.ex,second.1.2⟩)=⟨s.2.ex,r⟩ ∧
    boolEncodingRollback before.journal.length second.2=before := by
  rw [representedSourceStep_nonstatic F p s r static]
  dsimp only
  rw [representedSourceStep_nonstatic F child _ _ static]
  constructor
  · exact companionRollback_outer_commit ⟨s.2.ex,r⟩ [p.packed.sourceOp] [child.packed.sourceOp]
      [p.packed.residualUpdate] [child.packed.residualUpdate] F.this F.this 0 [] false
  · let xs := encodingWrites (selectedSlotPaths (if q.transient then ts q.address else ps q.address) q.slot)
      q.transient q.address (fun _ => q.raw) before
    let ys := encodingWrites (selectedSlotPaths (if next.transient then ts next.address else ps next.address) next.slot)
      next.transient next.address (fun _ => next.raw) (boolEncodingRun before xs)
    have restore := boolEncodingRollback_run before (xs++ys)
    rw [boolEncodingRun_append] at restore
    exact restore

end Solidity.Yul.Views
