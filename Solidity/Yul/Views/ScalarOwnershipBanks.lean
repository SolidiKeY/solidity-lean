import Solidity.Yul.Views.ScalarOwnershipFollowing
import Solidity.Yul.Views.GenericFlow.Banks

namespace Solidity.Yul.Views

/-- Same actual successful canonical preparation in a static source frame.
This constructs readLen provenance afresh; it does not infer source refusal
from unrestricted Source.Op application. -/
def ScalarOwnershipPlan.asStatic {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    ScalarOwnershipPlan {F with static := true} layout fixed written value s r :=
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  have roots : finiteView layout.registrations (s.2.ex.world.accounts F.this).storage p.raw :=
    fun c member => view c (layout.scalarFamilySourceInventory_roots F fixed s p.old p.oldComputed c member)
  ⟨p.old,(layout.scalarFamilySourceInventory_view {F with static := true} fixed s p.raw roots).trans
      (congrArg some p.old_agrees.symm),p.raw,p.encoded,p.oldChecked,p.nextChecked,p.sourceOp,p.prepared⟩

theorem ScalarOwnershipPlan.static_preserves_both {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    p.asStatic.step = ((.error (.revert []),s),r) := p.asStatic.static rfl

/-- The complete represented persistent map survives the ACTUAL transaction
finalization; transient source cells, transient complement and journals reset
by the existing companionEndTx contract (ScalarOwnershipPlan.endTx). -/
theorem ScalarOwnershipPlan.endTx_reencode {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteEncode p.next ((companionEndTx p.after).source.world.accounts F.this).storage
      (fun q => (companionEndTx p.after).residual.cells (complementKey false F.this q)) = some p.nextRaw :=
  GenericFlow.Banks.endTx_reencode p p.nextChecked static

theorem ScalarOwnershipPlan.transient_unchanged {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    p.after.source.transient = s.2.ex.transient :=
  GenericFlow.Banks.transient_unchanged p

/-- Unchanged physical input preserves the WHOLE administrative store, including
None versus explicit-default cells. Ordinary Source.applyOp still journals the
account operation; this is deliberately not whole EMState identity. -/
theorem ScalarOwnershipPlan.same_word_store {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (sameWord : p.raw written = value) :
    (p.after.source.world.accounts F.this).storage = (s.2.ex.world.accounts F.this).storage := by
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  rw [p.old_agrees] at view
  have checked : packedSeparationCheck (layout.scalarFamilySnapshot fixed p.raw) = true := by
    rw [← p.old_agrees]
    exact p.oldChecked
  have unchanged := layout.scalarFamily_unchanged fixed p.raw (s.2.ex.world.accounts F.this).storage checked view
  exact GenericFlow.Banks.same_word_store p sameWord
    (fun raw => layout.scalarFamilySnapshotWriteback fixed raw (s.2.ex.world.accounts F.this).storage)
    _ unchanged (p.pure_connection static)

end Solidity.Yul.Views
