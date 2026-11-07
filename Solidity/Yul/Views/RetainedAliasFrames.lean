import Solidity.Yul.Views.RetainedAliasSequence

/-! Existing paired frames transported through actual two-program execution.
Child boundaries are derived from the reached Source/residual result. These
laws restore external Source state and complementary journal only; arbitrary
caller locals, logs, heap restoration and call admission are not asserted. -/
namespace Solidity.Yul.Views.RetainedAliasFrames
open RetainedAliasOwnership RetainedAliasSequence

def paired {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership :=
  ⟨(executeThen p q).1.2.2.ex,(executeThen p q).2⟩

theorem before {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    : q.before=p.after := by
  first | (simp only;done) | skip
  unfold CapturedOwnershipPlan.before
  change (⟨(execute p).1.2.2.ex,(execute p).2⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)=p.after
  exact RetainedAliasOwnership.companion p

theorem after {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) : paired p q=q.after := by
  unfold paired
  rw [RetainedAliasSequence.next p q allowed]
  exact RetainedAliasOwnership.companion q

theorem child_rollback {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) (allowed2 : F2.static=false) :
    companionRollback (companionEnter p.after F2.this F2.sender F2.value F2.cd F2.static) (paired p q)=p.after := by
  first | (simp only;done) | skip
  rw [after p q allowed,CapturedOwnershipPlan.companion q allowed2,before p q]
  exact companionRollback_run _ _ _ _ _ _ _ _

theorem committed_outer_rollback {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) (allowed2 : F2.static=false) :
    companionRollback (companionEnter p.before F.this F.sender F.value F.cd F.static)
      (companionCommit (companionEnter p.after F2.this F2.sender F2.value F2.cd F2.static) (paired p q))=p.before := by
  first | (simp only;done) | skip
  rw [after p q allowed,CapturedOwnershipPlan.companion q allowed2,before p q]
  have rolled := companionRollback_outer_commit p.before [p.sourceOp] [q.sourceOp] p.updates q.updates
    F.this F.sender F.value F.cd F.static
  dsimp only at rolled
  rw [←CapturedOwnershipPlan.companion p allowed] at rolled
  simpa only [companionCommit,Source.CallFrame.commit] using rolled

theorem child_reencode {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) (allowed2 : F2.static=false) :
    let restored := companionRollback (companionEnter p.after F2.this F2.sender F2.value F2.cd F2.static) (paired p q)
    finiteEncode p.next (restored.source.world.accounts F.this).storage
      (fun slot => restored.residual.cells (complementKey false F.this slot))=some p.nextRaw := by
  dsimp only
  rw [child_rollback p q allowed allowed2]
  exact p.reencode allowed

theorem outer_reencode {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) (allowed2 : F2.static=false) :
    let restored := companionRollback (companionEnter p.before F.this F.sender F.value F.cd F.static)
      (companionCommit (companionEnter p.after F2.this F2.sender F2.value F2.cd F2.static) (paired p q))
    finiteEncode p.old (restored.source.world.accounts F.this).storage
      (fun slot => restored.residual.cells (complementKey false F.this slot))=some p.raw := by
  dsimp only
  rw [committed_outer_rollback p q allowed allowed2]
  exact p.encoded
end Solidity.Yul.Views.RetainedAliasFrames
