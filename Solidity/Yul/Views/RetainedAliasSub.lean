import Solidity.Yul.Views.RetainedAliasFrames

/-! Actual local-context substitution around checked ownership sequencing.
The external source state and residual journal are the reached sequence pair;
caller locals are restored by Source.EM.sub on both success and halt. This is
local-context transport, not external-call admission or complete capture. -/
namespace Solidity.Yul.Views.RetainedAliasSub
open RetainedAliasOwnership RetainedAliasSequence

def execute {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (caller : Source.Locals E.layout Δ) :=
  ((Source.EM.sub s.1 (program G F n dst src p.sourceOp >>= fun _ =>
    program G2 F2 n2 dst2 src2 q.sourceOp)).run (caller,s.2),(executeThen p q).2)

theorem actual {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (caller : Source.Locals E.layout Δ) :
    execute p q caller=
      (((match (executeThen p q).1.1 with
        | .ok value => .ok (value,(executeThen p q).1.2.1)
        | .error halt => .error halt),
        (caller,(executeThen p q).1.2.2)),(executeThen p q).2) := by
  first | (simp only;done) | skip
  unfold execute
  rw [actualSub_endpoints,←RetainedAliasSequence.source p q]
  rcases executeThen p q with ⟨⟨result,state⟩,journal⟩
  cases result <;> rfl

theorem caller {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (locals : Source.Locals E.layout Δ) :
    (execute p q locals).1.2.1=locals := by
  rw [actual p q locals]

theorem pair {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (locals : Source.Locals E.layout Δ) :
    (⟨(execute p q locals).1.2.2.ex,(execute p q locals).2⟩ :
      ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)=RetainedAliasFrames.paired p q := by
  rw [actual p q locals]
  rfl

theorem reencode {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (locals : Source.Locals E.layout Δ)
    (allowed : F.static=false) (allowed2 : F2.static=false) :
    finiteEncode q.next ((execute p q locals).1.2.2.ex.world.accounts F2.this).storage
      (fun slot => (execute p q locals).2.cells (complementKey false F2.this slot))=some q.nextRaw := by
  rw [actual p q locals]
  exact RetainedAliasSequence.reencode p q allowed allowed2

theorem late_static {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (locals : Source.Locals E.layout Δ)
    (allowed : F.static=false) (blocked : F2.static=true) :
    execute p q locals=((.error (.revert []),(locals,(RetainedAliasOwnership.execute p).1.2.2)),
      (RetainedAliasOwnership.execute p).2) := by
  rw [actual p q locals,RetainedAliasSequence.late_static p q allowed blocked]

theorem rollback {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (locals : Source.Locals E.layout Δ)
    (allowed : F.static=false) (allowed2 : F2.static=false) :
    companionRollback (companionEnter p.after F2.this F2.sender F2.value F2.cd F2.static)
      (⟨(execute p q locals).1.2.2.ex,(execute p q locals).2⟩ :
        ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)=p.after := by
  rw [pair p q locals]
  exact RetainedAliasFrames.child_rollback p q allowed allowed2

end Solidity.Yul.Views.RetainedAliasSub
