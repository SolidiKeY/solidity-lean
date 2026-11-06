import Solidity.Yul.Views.IntOwnershipPlan

namespace Solidity.Yul.Views

def IntOwnershipPlan.before {E ds d active Γ F layout fixed written value s r}
    (_ : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨s.2.ex,r⟩

def IntOwnershipPlan.after {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨p.step.1.2.2.ex,p.step.2⟩

theorem IntOwnershipPlan.companion {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    p.after = companionRunResidual (companionRunSource p.before [p.sourceOp]) p.updates := by
  unfold after
  rw [p.nonstatic static]
  rfl

/-- Pure changing-inventory writeback and actual journaled source execution
produce the SAME whole store and SAME complementary map. -/
theorem IntOwnershipPlan.pure_connection {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    layout.integerSnapshotWriteback fixed p.nextRaw (s.2.ex.world.accounts F.this).storage =
      some ((p.step.1.2.2.ex.world.accounts F.this).storage,fun q => p.step.2.cells (complementKey false F.this q)) := by
  unfold ComputedStorage.integerSnapshotWriteback
  dsimp only
  rw [show layout.integerSnapshot fixed p.nextRaw = p.next from rfl]
  have checked : packedSeparationCheck p.next = true := p.nextChecked
  rw [checked]
  obtain ⟨out,decoded,actual,_,_⟩ := finiteAccountWrite_actual F.this p.next p.nextRaw s.2.ex p.sourceOp p.prepared
  rw [p.nonstatic static]
  change packedStoreWriteback p.next p.nextRaw _ = some (((s.2.ex.apply p.sourceOp).world.accounts F.this).storage,_)
  rw [actual]
  unfold packedStoreWriteback
  rw [decoded,Option.map_some]
  apply congrArg (fun m => some (out,m))
  exact (ownership_transport_slice p.old p.next _ r false F.this p.raw p.encoded written value).symm

theorem IntOwnershipPlan.rollback {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (caller : Roadmap.Address) (amount : Roadmap.Word) (input : Roadmap.Bytes) :
    companionRollback (companionEnter p.before F.this caller amount input false) p.after = p.before := by
  rw [p.companion static]
  exact companionRollback_run _ _ _ _ _ _ _ _

theorem IntOwnershipPlan.child_rollback {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r)
    {qslot qvalue} (child : IntOwnershipPlan F layout fixed qslot qvalue p.step.1.2 p.step.2)
    (static : F.static = false) :
    companionRollback (companionEnter p.after F.this F.this 0 [] false) child.after = p.after := by
  rw [child.companion static]
  exact companionRollback_run _ _ _ _ _ _ _ _

theorem IntOwnershipPlan.committed_child_outer_rollback {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r)
    {qslot qvalue} (child : IntOwnershipPlan F layout fixed qslot qvalue p.step.1.2 p.step.2)
    (static : F.static = false) :
    companionRollback (companionEnter p.before F.this F.this 0 [] false)
      (companionCommit (companionEnter p.after F.this F.this 0 [] false) child.after) = p.before := by
  rw [child.companion static]
  change companionRollback (companionEnter p.before F.this F.this 0 [] false)
    (companionCommit (companionEnter p.after F.this F.this 0 [] false)
      (companionRunResidual (companionRunSource p.after [child.sourceOp]) child.updates)) = p.before
  rw [p.companion static]
  exact companionRollback_outer_commit p.before [p.sourceOp] [child.sourceOp] p.updates child.updates F.this F.this 0 [] false

theorem IntOwnershipPlan.other_key {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (k : ResidualKey complementCarrierOwnership) (other : k.transient ≠ false ∨ k.address ≠ F.this) :
    p.step.2.cells k = r.cells k := by
  cases static : F.static
  · rw [p.nonstatic static]
    apply residualRun_other
    intro w member same
    obtain ⟨slot,_,equal⟩ := List.mem_map.mp member
    subst w
    rcases other with bank | account
    · exact bank (congrArg ResidualKey.transient same)
    · exact account (congrArg ResidualKey.address same)
  · rw [p.static static]

theorem IntOwnershipPlan.endTx {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (q : Roadmap.Word) :
    (companionEndTx p.after).source.world = p.after.source.world ∧
    (companionEndTx p.after).residual.cells (complementKey false F.this q) = p.after.residual.cells (complementKey false F.this q) ∧
    (companionEndTx p.after).source.transient = Source.Transient.empty ∧
    (companionEndTx p.after).residual.cells (complementKey true F.this q) = 0 ∧
    (companionEndTx p.after).source.journal = [] ∧ (companionEndTx p.after).residual.journal = [] :=
  ⟨rfl,residualEndTx_persistent _ _ rfl,rfl,residualEndTx_transient _ _ rfl,rfl,rfl⟩

end Solidity.Yul.Views

namespace Solidity.Yul.Views

/-- Recomputed ownership after an actual successful step gives the SAME raw
map for the next step. This is derived, not a desired trace-consistency input. -/
theorem IntOwnershipPlan.following_raw {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r)
    {qslot qvalue} (child : IntOwnershipPlan F layout fixed qslot qvalue p.step.1.2 p.step.2)
    (static : F.static = false) : child.raw = p.nextRaw := by
  have view := p.view static
  have roots : finiteView layout.registrations (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw := by
    intro c member
    exact view c (layout.integer_root_member fixed p.nextRaw c member)
  have sameOld := Option.some.inj (child.oldComputed.symm.trans (layout.integerSourceInventory_view F fixed p.step.1.2 p.nextRaw roots))
  have encoded := child.encoded
  rw [sameOld] at encoded
  exact Option.some.inj (encoded.symm.trans (p.reencode static))

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem IntOwnershipPlan.raw_from_encoding {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (m : SlotView)
    (roots : finiteView layout.registrations (s.2.ex.world.accounts F.this).storage m)
    (encoded : finiteEncode (layout.integerSnapshot fixed m) (s.2.ex.world.accounts F.this).storage
      (fun q => r.cells (complementKey false F.this q)) = some m) : p.raw = m := by
  have old := Option.some.inj (p.oldComputed.symm.trans (layout.integerSourceInventory_view F fixed s m roots))
  have actual := p.encoded
  rw [old] at actual
  exact Option.some.inj (actual.symm.trans encoded)

end Solidity.Yul.Views
