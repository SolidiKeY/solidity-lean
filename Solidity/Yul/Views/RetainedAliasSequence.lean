import Solidity.Yul.Views.RetainedAliasOwnership

/-! Chronological composition of actual checked alias/storage programs. The
second plan consumes the first actual Source state, complementary journal and
capture scopes. Failure never resets a successful prefix to the original
journal. This is explicit sequencing, not general call instrumentation. -/
namespace Solidity.Yul.Views.RetainedAliasSequence
open Solidity.Backend.MemoryOps RetainedAliasOwnership

abbrev NextPlan {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2} (G2 : Source.Glob E) (F2 : Source.Fr) (n2 : Nat)
    (dst2 src2 : Source.Idx Γ σ2) (layout2 : @RetainedArrayLayout E τ2 b2 child2 active2 F2.this)
    (fixed2 : Roadmap.Evm.Fixed) (history2 : RetainedIndexHistory layout2) (written2 word2 : Roadmap.Word) :=
  Plan G2 F2 n2 (execute p).1.2 dst2 src2
    (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2
    layout2 fixed2 history2 written2 word2 (execute p).2

def executeThen {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) :=
  let first := execute p
  match first.1.1 with
  | .error h => ((Except.error h,first.1.2),first.2)
  | .ok _ => execute q

private theorem bind_status {E Γ α β} (m : Source.EM E Γ α) (k : Source.EM E Γ β) (s : Source.EMState E Γ) :
    (m >>= fun _ => k).run s=match (m.run s).1 with
      | .error h => (.error h,(m.run s).2)
      | .ok _ => k.run (m.run s).2 := by
  first | (simp only;done) | skip
  rw [Source.Hoare.run_bind]
  rcases m.run s with ⟨result,after⟩
  cases result <;> rfl

/-- No independent Source runs are assumed: this is the actual owner bind. -/
theorem source {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) :
    (executeThen p q).1=(program G F n dst src p.sourceOp >>= fun _ => program G2 F2 n2 dst2 src2 q.sourceOp).run s := by
  first | (simp only;done) | skip
  rw [bind_status]
  unfold executeThen RetainedAliasOwnership.execute
  dsimp only
  split <;> rename_i result status <;> simp only [status]

/-- A successful first step advances to the second plan's actual input. -/
theorem next {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) : executeThen p q=execute q := by
  first | (simp only;done) | skip
  have status : (execute p).1.1=.ok (s.1.get src) := by rw [nonstatic p allowed]
  unfold executeThen
  dsimp only
  split
  · rename_i h failed
    have impossible := failed.symm.trans status
    cases impossible
  · rfl

/-- Late static refusal retains the FIRST reached journal and source store,
plus the second completed alias assignment. -/
theorem late_static {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) (blocked : F2.static=true) :
    executeThen p q=((.error (.revert []),((execute p).1.2.1.set dst2 ((execute p).1.2.1.get src2),(execute p).1.2.2)),(execute p).2) := by
  rw [next p q allowed]
  exact RetainedAliasOwnership.static q blocked

/-- The first completed physical map remains represented after late refusal. -/
theorem late_static_reencode {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) (blocked : F2.static=true) :
    finiteEncode p.next ((executeThen p q).1.2.2.ex.world.accounts F.this).storage
      (fun slot => (executeThen p q).2.cells (complementKey false F.this slot))=some p.nextRaw := by
  rw [late_static p q allowed blocked]
  exact reencode p allowed

/-- On two successes the second plan's completed map is the actual final map. -/
theorem reencode {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (allowed : F.static=false) (allowed2 : F2.static=false) :
    finiteEncode q.next ((executeThen p q).1.2.2.ex.world.accounts F2.this).storage
      (fun slot => (executeThen p q).2.cells (complementKey false F2.this slot))=some q.nextRaw := by
  rw [next p q allowed]
  exact RetainedAliasOwnership.reencode q allowed2

/-- Actual owner safety composes on both success and error branches. -/
theorem MemOK {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) : Source.MemOK E H (executeThen p q).1.2 := by
  first | (simp only;done) | skip
  unfold executeThen
  dsimp only
  split
  · exact RetainedAliasOwnership.MemOK p H ok
  · exact RetainedAliasOwnership.MemOK q H (RetainedAliasOwnership.MemOK p H ok)

/-- First refusal skips the entire second alias and operation. -/
theorem first_static {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2)
    (blocked : F.static=true) :
    executeThen p q=((.error (.revert []),(execute p).1.2),(execute p).2) := by
  first | (simp only;done) | skip
  have status : (execute p).1.1=.error (.revert []) := by rw [RetainedAliasOwnership.static p blocked]
  unfold executeThen
  dsimp only
  split
  · rename_i h failed
    have same := Except.error.inj (failed.symm.trans status)
    rw [same]
  · rename_i v succeeded
    have impossible := succeeded.symm.trans status
    cases impossible

/-- The next producer keeps the actual first observation prefix. -/
theorem capture_prefix {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {σ2 : Source.STy} (G2 : Source.Glob E) (F2 : Source.Fr) (n2 : Nat) (dst2 src2 : Source.Idx Γ σ2)
    (scope : EntryReferenceScope E)
    (member : scope ∈ (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2) :
    scope ∈ (captureEvaluatedValue G2 F2 (n2+2) (sourceLocalAlias dst2 src2)
      (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2 (execute p).1.2).2 := by
  exact captureValueRun_prefix F2 _ (RetainedLocalAlias.value G2 F2 n2 dst2 src2) (execute p).1.2 scope member

/-- Existing checked computation fields reproduce the public preparation. -/
theorem checked_prepared {E τ b child active Γ F layout fixed history scopes written word s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written word s r) :
    prepareCapturedOwnership? F layout fixed history scopes written word s r=some p := by
  unfold prepareCapturedOwnership?
  split
  · rename_i missing
    rw [p.lengthComputed] at missing
    cases missing
  · rename_i len computed
    have same := Option.some.inj (computed.symm.trans p.lengthComputed)
    subst len
    split
    · rename_i missing
      rw [p.oldImageComputed] at missing
      cases missing
    · rename_i oldImage computed
      have same := Option.some.inj (computed.symm.trans p.oldImageComputed)
      subst oldImage
      split
      · rename_i missing
        rw [p.oldComputed] at missing
        cases missing
      · rename_i old computed
        have same := Option.some.inj (computed.symm.trans p.oldComputed)
        subst old
        split
        · rename_i missing
          rw [p.encoded] at missing
          cases missing
        · rename_i raw computed
          have same := Option.some.inj (computed.symm.trans p.encoded)
          subst raw
          split
          ·
            split
            · rename_i missing
              rw [p.nextImageComputed] at missing
              cases missing
            · rename_i nextImage computed
              have same := Option.some.inj (computed.symm.trans p.nextImageComputed)
              subst nextImage
              split
              ·
                split
                · rename_i missing
                  rw [p.prepared] at missing
                  cases missing
                · rename_i op computed
                  have same := Option.some.inj (computed.symm.trans p.prepared)
                  subst op
                  rfl
              · rename_i rejected
                exact False.elim (rejected p.nextChecked)
          · rename_i rejected
            exact False.elim (rejected p.oldChecked)
end Solidity.Yul.Views.RetainedAliasSequence
