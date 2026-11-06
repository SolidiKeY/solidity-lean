import Solidity.Yul.Views.OwnedBoolOwnership

namespace Solidity.Yul.Views

def RepresentedOwnershipPlan.after {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨p.step.1.1.2.2.ex,p.step.1.2⟩

theorem RepresentedOwnershipPlan.after_split {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    p.after=companionRunResidual (companionRunSource ⟨s.2.ex,r⟩ [p.sourceOp]) p.updates := by
  unfold after
  rw [p.nonstatic static]
  rfl

theorem RepresentedOwnershipPlan.refreshed {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    layout.primitiveSourceInventory? F fixed p.step.1.1.2=some (layout.primitiveSnapshot fixed p.nextRaw) :=
  layout.primitiveInventory_represented F fixed p.step.1.1.2 _ p.nextEncoding p.nextRaw
    (fun c member => layout.primitive_root_member fixed p.nextRaw c member) (p.view static)

/-- Exact owned-byte choices for each live field derive from the next raw map;
old keys dropped on shrink remain latent and outside the live view. -/
theorem RepresentedOwnershipPlan.owned_codes {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false)
    (c) (member : c ∈ layout.primitiveSnapshot fixed p.nextRaw) :
    p.step.2.cells (ownedByteKey false F.this c)=chosenPathCode c (encoding.cells (ownedByteKey false F.this c)) p.nextRaw := by
  rw [p.nonstatic static]
  exact encodingWrites_result _ _ _ _ _ ((packedSeparationCheck_iff _).mp p.nextChecked) c member

theorem RepresentedOwnershipPlan.owned_other {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false)
    (key) (outside : ∀ c ∈ layout.primitiveSnapshot fixed p.nextRaw, key≠ownedByteKey false F.this c) :
    p.step.2.cells key=encoding.cells key := by
  rw [p.nonstatic static]
  exact encodingWrites_other _ _ _ _ _ _ key outside

theorem RepresentedOwnershipPlan.rollback {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.this 0 [] false) p.after=⟨s.2.ex,r⟩ ∧
    boolEncodingRollback encoding.journal.length p.step.2=encoding := by
  constructor
  · rw [p.after_split static]
    exact companionRollback_run _ _ _ _ _ _ _ _
  · rw [p.nonstatic static]
    exact boolEncodingRollback_run encoding _

theorem RepresentedOwnershipPlan.unchanged_encoding {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (sameWord : p.raw written=value) : p.nextEncoding=encoding := by
  have sameRaw : p.nextRaw=p.raw := by
    funext q
    by_cases same : q=written
    · subst q
      exact (find_saveSlot p.raw written value).trans sameWord.symm
    · exact find_saveSlot_other _ _ _ _ same
  have view := finiteEncode_view _ _ _ p.raw
    (representedRegistry_separated _ _ _ _ ((packedSeparationCheck_iff _).mp p.oldChecked)) p.encoded
  unfold nextEncoding primitiveEncodingNext
  rw [sameRaw,← p.old_agrees,encodingWrites_unchanged _ _ _ _ _ _ view]
  rfl

theorem RepresentedOwnershipPlan.same_word_store {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (static : F.static=false) (sameWord : p.raw written=value) :
    (p.after.source.world.accounts F.this).storage=(s.2.ex.world.accounts F.this).storage := by
  have sameRaw : p.nextRaw=p.raw := by
    funext q
    by_cases same : q=written
    · subst q
      exact (find_saveSlot p.raw written value).trans sameWord.symm
    · exact find_saveSlot_other _ _ _ _ same
  have view := finiteEncode_view _ _ _ p.raw
    (representedRegistry_separated _ _ _ _ ((packedSeparationCheck_iff _).mp p.oldChecked)) p.encoded
  have nextView : finiteView p.next (s.2.ex.world.accounts F.this).storage p.nextRaw := by
    unfold next
    rw [sameRaw,p.unchanged_encoding sameWord,← p.old_agrees]
    exact view
  unfold after
  rw [p.nonstatic static]
  exact finiteAccountWrite_unchanged F.this p.next p.nextRaw s.2.ex p.sourceOp p.prepared nextView

end Solidity.Yul.Views
