import Solidity.Yul.Views.RecursiveOwnershipFollowing

namespace Solidity.Yul.Views

/-- Same actual successful canonical preparation in a static source frame.
This constructs readLen provenance afresh; it does not infer source refusal
from unrestricted Source.Op application. -/
def RecursiveOwnershipPlan.asStatic {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    RecursiveOwnershipPlan {F with static := true} layout fixed written value s r :=
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  have roots : finiteView layout.registrations (s.2.ex.world.accounts F.this).storage p.raw :=
    fun c member => view c (layout.sourceInventory_roots F fixed s p.old p.oldComputed c member)
  ⟨p.old,(layout.sourceInventory_view {F with static := true} fixed s p.raw roots).trans
      (congrArg some p.old_agrees.symm),p.raw,p.encoded,p.oldChecked,p.nextChecked,p.sourceOp,p.prepared⟩

theorem RecursiveOwnershipPlan.static_preserves_both {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    p.asStatic.step = ((.error (.revert []),s),r) := p.asStatic.static rfl

/-- The complete represented persistent map survives the ACTUAL transaction
finalization; transient source cells, transient complement and journals reset
by the existing companionEndTx contract (RecursiveOwnershipPlan.endTx). -/
theorem RecursiveOwnershipPlan.endTx_reencode {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteEncode p.next ((companionEndTx p.after).source.world.accounts F.this).storage
      (fun q => (companionEndTx p.after).residual.cells (complementKey false F.this q)) = some p.nextRaw := by
  have same : (fun q => (companionEndTx p.after).residual.cells (complementKey false F.this q)) =
      (fun q => p.after.residual.cells (complementKey false F.this q)) := by
    funext q
    exact residualEndTx_persistent _ _ rfl
  rw [same]
  exact p.reencode static

theorem RecursiveOwnershipPlan.transient_unchanged {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    p.after.source.transient = s.2.ex.transient := by
  cases static : F.static
  · obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp p.prepared
    unfold RecursiveOwnershipPlan.after
    rw [p.nonstatic static,← same]
    rfl
  · unfold RecursiveOwnershipPlan.after
    rw [p.static static]

/-- Unchanged physical input preserves the WHOLE administrative store, including
None versus explicit-default cells. Ordinary Source.applyOp still journals the
account operation; this is deliberately not whole EMState identity. -/
theorem RecursiveOwnershipPlan.same_word_store {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (sameWord : p.raw written = value) :
    (p.after.source.world.accounts F.this).storage = (s.2.ex.world.accounts F.this).storage := by
  have rawSame : p.nextRaw = p.raw := by
    funext q
    by_cases same : q = written
    · subst q
      exact (find_saveSlot p.raw written value).trans sameWord.symm
    · exact find_saveSlot_other p.raw written q value same
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  rw [p.old_agrees] at view
  have checked : packedSeparationCheck (layout.snapshot fixed p.raw) = true := by
    rw [← p.old_agrees]
    exact p.oldChecked
  have unchanged := layout.snapshot_unchanged fixed p.raw (s.2.ex.world.accounts F.this).storage checked view
  have actual := p.pure_connection static
  rw [rawSame] at actual
  exact congrArg Prod.fst (Option.some.inj (actual.symm.trans unchanged))

end Solidity.Yul.Views
