import Solidity.Yul.Views.RetainedAliasFrames

/-! An explicit successful Source sequence followed by the existing endTx
state update. Errors retain their actual reached prefix; this adapter is not
transaction dispatch, admission, failure rollback or general call capture. -/
namespace Solidity.Yul.Views.RetainedAliasTransaction
open RetainedAliasOwnership RetainedAliasSequence

/-- The same Source state update used at successful transaction finalization. -/
def finish {E Γ α} (v : α) : Source.EM E Γ α := do
  Source.EM.modSt fun s => {s with ex:=s.ex.endTx}
  pure v

theorem finish_run {E Γ α} (v : α) (s : Source.EMState E Γ) :
    (finish v).run s=(.ok v,(s.1,{s.2 with ex:=s.2.ex.endTx})) := by rfl

def execute {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) :=
  let reached := executeThen p q
  match reached.1.1 with
  | .error _ => reached
  | .ok v => ((finish v).run reached.1.2,residualEndTx reached.2)

theorem source {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) :
    (execute p q).1=
      ((program G F n dst src p.sourceOp >>= fun _ => program G2 F2 n2 dst2 src2 q.sourceOp) >>= finish).run s := by
  first | (simp only;done) | skip
  rw [Source.Hoare.run_bind,←RetainedAliasSequence.source p q]
  unfold execute
  rcases actual : executeThen p q with ⟨⟨result,state⟩,journal⟩
  cases result <;> rfl

theorem success {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) (allowed : F.static=false) (allowed2 : F2.static=false) :
    execute p q=
      ((.ok ((RetainedAliasOwnership.execute p).1.2.1.get src2),
        ((RetainedAliasOwnership.execute q).1.2.1,
          {(RetainedAliasOwnership.execute q).1.2.2 with ex:=(RetainedAliasOwnership.execute q).1.2.2.ex.endTx})),
        residualEndTx (RetainedAliasOwnership.execute q).2) := by
  first | (simp only;done) | skip
  unfold execute
  rw [RetainedAliasSequence.next p q allowed,RetainedAliasOwnership.nonstatic q allowed2]
  rfl

theorem failure {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {halt} (failed : (executeThen p q).1.1=.error halt) :
    execute p q=executeThen p q := by
  simp only [execute,failed]

theorem persistent {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) (allowed : F.static=false) (allowed2 : F2.static=false) :
    finiteEncode q.next ((execute p q).1.2.2.ex.world.accounts F2.this).storage
      (fun slot => (execute p q).2.cells (complementKey false F2.this slot))=some q.nextRaw := by
  first | (simp only;done) | skip
  rw [success p q allowed allowed2]
  change finiteEncode q.next ((RetainedAliasOwnership.execute q).1.2.2.ex.world.accounts F2.this).storage
    (fun slot => (residualEndTx (RetainedAliasOwnership.execute q).2).cells (complementKey false F2.this slot))=some q.nextRaw
  have cells : (fun slot => (residualEndTx (RetainedAliasOwnership.execute q).2).cells (complementKey false F2.this slot))=
      (fun slot => (RetainedAliasOwnership.execute q).2.cells (complementKey false F2.this slot)) := by
    funext slot
    exact residualEndTx_persistent _ _ rfl
  rw [cells]
  exact RetainedAliasOwnership.reencode q allowed2

theorem reset {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) (allowed : F.static=false) (allowed2 : F2.static=false)
    (address : Roadmap.Address) (slot : Roadmap.Word) :
    (execute p q).1.2.2.ex.transient=Source.Transient.empty ∧
    (execute p q).2.cells (complementKey true address slot)=0 ∧
    (execute p q).1.2.2.ex.journal=[] ∧ (execute p q).2.journal=[] := by
  rw [success p q allowed allowed2]
  exact ⟨rfl,residualEndTx_transient _ _ rfl,rfl,rfl⟩


theorem finish_MemOK {E Γ α} (v : α) (s : Source.EMState E Γ)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((finish v).run s).2 := by
  first | (simp only;done) | skip
  rw [finish_run]
  exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2⟩

theorem MemOK {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (execute p q).1.2 := by
  first | (simp only;done) | skip
  have safe := RetainedAliasSequence.MemOK p q H ok
  unfold execute
  rcases actual : executeThen p q with ⟨⟨result,state⟩,journal⟩
  rw [actual] at safe
  cases result with
  | error halt => exact safe
  | ok value => exact finish_MemOK value state H safe

end Solidity.Yul.Views.RetainedAliasTransaction
