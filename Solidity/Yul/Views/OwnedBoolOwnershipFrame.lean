import Solidity.Yul.Views.OwnedBoolFollowing

namespace Solidity.Yul.Views

def RepresentedOwnershipPlan.asStatic {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :
    RepresentedOwnershipPlan {F with static:=true} layout fixed written value s r encoding :=
  have view := finiteEncode_view _ _ _ p.raw
    (representedRegistry_separated _ _ _ _ ((packedSeparationCheck_iff _).mp p.oldChecked)) p.encoded
  ⟨p.old,(layout.primitiveInventory_represented {F with static:=true} fixed s p.old encoding p.raw
      (fun c member => layout.primitiveSourceInventory_roots F fixed s p.old p.oldComputed c member) view).trans
      (congrArg some p.old_agrees.symm),p.raw,p.encoded,p.oldChecked,p.nextChecked,p.sourceOp,p.prepared⟩

theorem RepresentedOwnershipPlan.static_preserves_three {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :
    p.asStatic.step=(((.error (.revert []),s),r),encoding) := p.asStatic.static rfl

theorem RepresentedOwnershipPlan.other_account {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (a : Roadmap.Address) (different : a≠F.this) : p.after.source.world.accounts a=s.2.ex.world.accounts a := by
  cases static : F.static
  · obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp p.prepared
    unfold after
    rw [p.nonstatic static,← same]
    exact Source.World.set_other _ different _
  · unfold after
    rw [p.static static]

theorem RepresentedOwnershipPlan.other_residual {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (key : ResidualKey complementCarrierOwnership) (different : key.transient≠false ∨ key.address≠F.this) :
    p.step.1.2.cells key=r.cells key := by
  cases static : F.static
  · rw [p.nonstatic static]
    apply residualRun_other
    intro w member same
    obtain ⟨slot,_,equal⟩ := List.mem_map.mp member
    subst w
    rcases different with bank | account
    · exact bank (congrArg ResidualKey.transient same)
    · exact account (congrArg ResidualKey.address same)
  · rw [p.static static]

theorem RepresentedOwnershipPlan.child_outer_rollback {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    {q v} (child : RepresentedOwnershipPlan F layout fixed q v p.step.1.1.2 p.step.1.2 p.step.2)
    (static : F.static=false) :
    companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.this 0 [] false)
      (companionCommit (companionEnter p.after F.this F.this 0 [] false) child.after)=⟨s.2.ex,r⟩ ∧
    boolEncodingRollback encoding.journal.length child.step.2=encoding := by
  constructor
  · rw [child.after_split static]
    change companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.this 0 [] false)
      (companionCommit (companionEnter p.after F.this F.this 0 [] false)
        (companionRunResidual (companionRunSource p.after [child.sourceOp]) child.updates))=⟨s.2.ex,r⟩
    rw [p.after_split static]
    exact companionRollback_outer_commit _ _ _ _ _ _ _ _ _ _
  · have first : p.step.2=p.nextEncoding := congrArg Prod.snd (p.nonstatic static)
    have second : child.step.2=child.nextEncoding := congrArg Prod.snd (child.nonstatic static)
    let xs := encodingWrites (layout.primitiveSnapshot fixed p.nextRaw) false F.this p.nextRaw encoding
    let ys := encodingWrites (layout.primitiveSnapshot fixed child.nextRaw) false F.this child.nextRaw p.step.2
    have restore := boolEncodingRollback_run encoding (xs++ys)
    rw [boolEncodingRun_append] at restore
    have joined : child.nextEncoding=boolEncodingRun (boolEncodingRun encoding xs) ys :=
      congrArg (fun before => boolEncodingRun before ys) first
    exact (congrArg (boolEncodingRollback encoding.journal.length) (second.trans joined)).trans restore

theorem representedRegistry_endTx_persistent {D L} (cs : List (ScalarPath D L)) (a) (encoding) :
    representedRegistry cs false a (boolEncodingEndTx encoding)=representedRegistry cs false a encoding := by
  apply List.map_congr_left
  intro c _
  rw [boolEncodingEndTx_persistent encoding (ownedByteKey false a c) rfl]

theorem RepresentedOwnershipPlan.endTx_reencode {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    finiteEncode (representedRegistry (layout.primitiveSnapshot fixed p.nextRaw) false F.this (boolEncodingEndTx p.step.2))
      ((companionEndTx p.after).source.world.accounts F.this).storage
      (fun q => (companionEndTx p.after).residual.cells (complementKey false F.this q))=some p.nextRaw := by
  rw [representedRegistry_endTx_persistent]
  have same : (fun q => (companionEndTx p.after).residual.cells (complementKey false F.this q))=
      (fun q => p.step.1.2.cells (complementKey false F.this q)) := by
    funext q
    exact residualEndTx_persistent _ _ rfl
  rw [same]
  exact p.reencode_current static

end Solidity.Yul.Views
